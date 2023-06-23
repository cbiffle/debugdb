//! Abstract, dynamic, JSON-like representation of Rust values.
//!
//! This can be read from a program image using `Load` even if the program doing
//! the reading doesn't know the type shape in advance.

use regex::Regex;

use crate::load::{choose_variant, load_unsigned, Load, LoadError, Machine};
use crate::{Encoding, Type, DebugDb, TypeId, EntityId};
use std::borrow::Cow;
use std::convert::TryFrom;
use std::fmt::Display;
use std::collections::{BTreeSet, BTreeMap};

#[derive(Clone, Debug)]
pub enum Value {
    Array(Vec<Value>),
    Base(Base),
    Struct(Struct),
    CEnum(CEnum),
    Enum(Enum),
    Pointer(Pointer),
}

impl Value {
    pub fn u64_value(&self) -> Option<u64> {
        if let Self::Base(b) = self {
            match b {
                Base::U8(x) => return Some(u64::from(*x)),
                Base::U32(x) => return Some(u64::from(*x)),
                Base::U64(x) => return Some(*x),
                _ => (),
            }
        }
        None
    }

    pub fn pointer_value(&self) -> Option<u64> {
        let Self::Pointer(p) = self else { return None; };
        Some(p.value)
    }

    pub fn newtype(&self, name: &str) -> Option<&Value> {
        let Self::Struct(s) = self else { return None };
        if s.name != name { return None; }
        if s.members.len() != 1 { return None };
        s.any_member_named("__0")
    }

    pub fn type_name(&self) -> Cow<'_, str> {
        match self {
            Self::Array(es) => {
                let elt_type = es.get(0)
                    .map(|v| v.type_name())
                    .unwrap_or("???".into());
                format!("[{}; {}]", elt_type, es.len()).into()
            }
            Self::Base(b) => match b {
                Base::U8(_) => "u8".into(),
                Base::U32(_) => "u32".into(),
                Base::U64(_) => "u64".into(),
                Base::Bool(_) => "bool".into(),
            },
            Self::Struct(s) => (&s.name).into(),
            Self::CEnum(s) => (&s.name).into(),
            Self::Enum(s) => (&s.name).into(),
            Self::Pointer(s) => (&s.name).into(),
        }
    }

    pub fn collect_names(&self, set: &mut BTreeSet<String>) {
        match self {
            Self::Array(v) => for elt in v {
                elt.collect_names(set);
            },
            Self::Base(_) => (),
            Self::Struct(s) => {
                set.insert(s.name.clone());
                for (_, value) in &s.members {
                    value.collect_names(set);
                }
            }
            Self::CEnum(e) => {
                set.insert(e.name.clone());
            }
            Self::Enum(e) => {
                set.insert(e.name.clone());
                // We are deliberately skipping the name of the variant struct.
                for (_, value) in &e.value.members {
                    value.collect_names(set);
                }
            }
            Self::Pointer(p) => {
                set.insert(p.name.clone());
            }
        }
    }

    fn text(&self, world: &DebugDb, indent: usize, use_table: &UseTable, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        match self {
            Self::Base(b) => match b {
                Base::U8(x) => write!(f, "{x}_u8"),
                Base::U32(x) => write!(f, "{x}_u32"),
                Base::U64(x) => write!(f, "{x}_u64"),
                Base::Bool(0) => write!(f, "false"),
                Base::Bool(1) => write!(f, "true"),
                Base::Bool(x) => write!(f, "{x}_bool"),
            },
            Self::Pointer(p) => {
                let nearest = world.entities_by_address(p.value)
                    .filter_map(|ar| if let EntityId::Var(v) = ar.entity {
                        Some((v, ar.range.clone()))
                    } else {
                        None
                    })
                    .min_by_key(|(_, range)| range.start.abs_diff(p.value));
                if let Some((vid, range)) = nearest {
                    let var = world.static_variable_by_id(vid).unwrap();
                    let name = &var.name;
                    let prefix = if p.is_probably_mut() {
                        "&mut "
                    } else {
                        "&"
                    };
                    write!(f, "{prefix}{name} /* {:#x} */ as {}", p.value, p.name)
                } else {
                    write!(f, "{:#x} as {}", p.value, p.name)
                }
            },
            Self::CEnum(e) => write!(f, "{}::{}", use_table.rewrite(&e.name), e.disc),
            Self::Array(v) => {
                // TODO: special-case bases for more compact printering
                writeln!(f, "[")?;
                for elt in v {
                    write!(f, "{:indent$}    ", "")?;
                    elt.text(world, indent + 4, use_table, f)?;
                    writeln!(f, ",")?;
                }
                write!(f, "{:indent$}]", "")
            }
            Self::Struct(s) => {
                if !display_dyn(world, s, f)? {
                    write!(f, "{}", use_table.rewrite(&s.name))?;
                    fmt_struct_body(s, world, indent, use_table, f)?;
                }
                Ok(())
            }
            Self::Enum(e) => {
                write!(f, "{}::{}", use_table.rewrite(&e.name), e.disc)?;
                fmt_struct_body(&e.value, world, indent, use_table, f)
            }
        }
    }
}

fn display_dyn(
    world: &DebugDb,
    s: &Struct,
    f: &mut core::fmt::Formatter,
) -> Result<bool, core::fmt::Error> {
    let dynptr = Regex::new(r#"^[&*](mut )?dyn (.*)$"#).unwrap();
    if s.members.len() != 2 { return Ok(false); }

    let Some(c) = dynptr.captures(&s.name) else { return Ok(false); };
    let _trait_name = &c[2];
    let ismut = &c[1];
    let Some((_, value)) = s.members.iter()
        .find(|(name, _)| name.as_ref().map(String::as_str) == Some("vtable"))
        else { return Ok(false); };

    let Some((_, dest)) = s.members.iter()
        .find(|(name, _)| name.as_ref().map(String::as_str) == Some("pointer"))
        else { return Ok(false); };

    let Some(addr) = value.pointer_value() else { return Ok(false); };
    let Some(dest_addr) = dest.pointer_value() else { return Ok(false); };

    for e in world.entities_by_address(addr) {
        if addr != e.range.start {
            continue;
        }
        let EntityId::Var(v) = e.entity else { return Ok(false); };
        let Some(v) = world.static_variable_by_id(v) else { return Ok(false); };

        let vtable = Regex::new(r#"^<(.*) as (.*)>::\{vtable\}$"#).unwrap();
        let Some(vc) = vtable.captures(&v.name) else { return Ok(false); };
        let concrete = &vc[1];
        let trait_name = &vc[2];

        write!(f, "{dest_addr:#x} as &{ismut}{concrete} as &{ismut}dyn {trait_name}")?;
        return Ok(true);
    }

    Ok(false)
}

fn fmt_struct_body(s: &Struct, world: &DebugDb, indent: usize, use_table: &UseTable, f: &mut core::fmt::Formatter) -> core::fmt::Result {
    if s.members.is_empty() {
        Ok(())
    } else if s.is_tuple_like() {
        if s.members.len() == 1 {
            write!(f, "(")?;
            for (_, value) in &s.members {
                value.text(world, indent, use_table, f)?;
            }
            write!(f, ")")
        } else {
            writeln!(f, "(")?;
            for (_, value) in &s.members {
                write!(f, "{:indent$}    ", "")?;
                value.text(world, indent + 4, use_table, f)?;
                writeln!(f, ",")?;
            }
            write!(f, "{:indent$})", "")
        }
    } else {
        writeln!(f, " {{")?;
        for (name, value) in &s.members {
            if let Some(name) = name {
                write!(f, "{:indent$}    {name}: ", "")?;
            } else {
                write!(f, "{:indent$}    _: ", "")?;
            }
            value.text(world, indent + 4, use_table, f)?;
            writeln!(f, ",")?;
        }
        write!(f, "{:indent$}}}", "")
    }
}

pub struct ValueWithDb<'a>(pub Value, pub &'a DebugDb);

impl Display for ValueWithDb<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        let mut names = BTreeSet::new();
        self.0.collect_names(&mut names);
        let use_table = UseTable::new(names);
        for (long, stub) in &use_table.0 {
            if long == stub {
                writeln!(f, "use {long};")?;
            } else {
                writeln!(f, "use {long} as {stub};")?;
            }
        }
        self.0.text(self.1, 0, &use_table, f)
    }
}

struct UseTable(BTreeMap<String, String>);

impl UseTable {
    fn new(names: BTreeSet<String>) -> Self {
        let simple = Regex::new(r#"^([a-zA-Z_0-9{}#]+::)*([A-Za-z0-9_]+)$"#).unwrap();
        let mut rewrites = BTreeMap::new();
        let mut taken = BTreeSet::new();
        for name in names {
            if let Some(c) = simple.captures(&name) {
                let stub = &c[2];
                if !taken.contains(stub) {
                    taken.insert(stub.to_string());
                    rewrites.insert(name.clone(), stub.to_string());
                }
            }
        }
        Self(rewrites)
    }

    fn rewrite<'a>(&'a self, name: &'a str) -> &str {
        self.0.get(name).map(String::as_str).unwrap_or(name)
    }
}

impl Load for Value {
    fn from_state<M: Machine>(
        machine: &M,
        addr: u64,
        world: &DebugDb,
        ty: &Type,
    ) -> Result<Self, LoadError<M::Error>> {
        match ty {
            Type::Base(_) => {
                Ok(Self::Base(Base::from_state(machine, addr, world, ty)?))
            }
            Type::Array(_) => {
                Ok(Self::Array(Vec::from_state(machine, addr, world, ty)?))
            }
            Type::Struct(_) => {
                Ok(Self::Struct(Struct::from_state(machine, addr, world, ty)?))
            }
            Type::CEnum(_) => {
                Ok(Self::CEnum(CEnum::from_state(machine, addr, world, ty)?))
            }
            Type::Enum(_) => {
                Ok(Self::Enum(Enum::from_state(machine, addr, world, ty)?))
            }
            Type::Pointer(_) => Ok(Self::Pointer(Pointer::from_state(
                machine, addr, world, ty,
            )?)),
            _ => unimplemented!(),
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub enum Base {
    U8(u8),
    U32(u32),
    U64(u64),
    Bool(u8),
}

impl Base {
    pub fn as_u64(self) -> Option<u64> {
        match self {
            Self::U8(x) => return Some(u64::from(x)),
            Self::U32(x) => return Some(u64::from(x)),
            Self::U64(x) => return Some(x),
            _ => None,
        }
    }
}

impl Load for Base {
    fn from_state<M: Machine>(
        machine: &M,
        addr: u64,
        world: &DebugDb,
        ty: &Type,
    ) -> Result<Self, LoadError<M::Error>> {
        let Type::Base(b) = ty else { return Err(LoadError::NotABase); };
        match (b.encoding, b.byte_size) {
            (Encoding::Unsigned, 1) => Ok(Base::U8(load_unsigned(
                world.endian(),
                machine,
                addr,
                1,
            )?.ok_or(LoadError::DataUnavailable)? as u8)),
            (Encoding::Unsigned, 4) => Ok(Base::U32(load_unsigned(
                world.endian(),
                machine,
                addr,
                4,
            )?.ok_or(LoadError::DataUnavailable)? as u32)),
            (Encoding::Unsigned, 8) => Ok(Base::U64(load_unsigned(
                world.endian(),
                machine,
                addr,
                8,
            )?.ok_or(LoadError::DataUnavailable)?)),
            (Encoding::Boolean, 1) => Ok(Base::Bool(load_unsigned(
                world.endian(),
                machine,
                addr,
                1,
            )?.ok_or(LoadError::DataUnavailable)? as u8)),
            _ => {
                println!("{:?} {}", b.encoding, b.byte_size);
                return Err(LoadError::UnsupportedType);
            },
        }
    }
}

#[derive(Clone, Debug)]
pub struct Struct {
    pub name: String,
    pub members: Vec<(Option<String>, Value)>,
}

impl Struct {
    // TODO: better to have a Value::Tuple and distinguish at creation
    pub fn is_tuple_like(&self) -> bool {
        for (name, _) in &self.members {
            let Some(name) = name else { return false; };
            if !name.starts_with("__") { return false; }
            if name[2..].parse::<u32>().is_err() {
                return false;
            }
        }
        true
    }

    pub fn members_named<'s, 'n>(&'s self, name: &'n str) -> impl Iterator<Item = &'s Value> + 'n
    where 's: 'n {
        self.members.iter()
            .filter(|(n, _)| n.as_deref() == Some(name))
            .map(|(_, value)| value)
    }

    pub fn any_member_named(&self, name: &str) -> Option<&Value> {
        self.members.iter()
            .find(|(n, _)| n.as_deref() == Some(name))
            .map(|(_, v)| v)
    }
}

impl Load for Struct {
    fn from_state<M: Machine>(
        machine: &M,
        addr: u64,
        world: &DebugDb,
        ty: &Type,
    ) -> Result<Self, LoadError<M::Error>> {
        let Type::Struct(s) = ty else { return Err(LoadError::NotAStruct); };
        let mut members = vec![];

        for m in &s.members {
            let t = world.type_by_id(m.type_id).unwrap();
            let ma = addr + m.location;
            let v = Value::from_state(machine, ma, world, t)?;
            members.push((m.name.clone(), v));
        }

        Ok(Self {
            name: s.name.clone(),
            members,
        })
    }
}

#[derive(Clone, Debug)]
pub struct Enum {
    pub name: String,
    pub disc: String,
    pub value: Struct,
}

impl Load for Enum {
    fn from_state<M: Machine>(
        machine: &M,
        addr: u64,
        world: &DebugDb,
        ty: &Type,
    ) -> Result<Self, LoadError<M::Error>> {
        let Type::Enum(s) = ty else { return Err(LoadError::NotAnEnum); };
        let v = choose_variant(machine, addr, world, s)?;

        let vtype_id = v.member.type_id;
        let vty = world.type_by_id(vtype_id).unwrap();
        let va = addr + v.member.location;
        let value = Struct::from_state(machine, va, world, vty)?;

        Ok(Self {
            name: s.name.clone(),
            disc: v.member.name.as_ref().unwrap().clone(),
            value,
        })
    }
}

#[derive(Clone, Debug)]
pub struct CEnum {
    name: String,
    disc: String,
}

impl Load for CEnum {
    fn from_state<M: Machine>(
        machine: &M,
        addr: u64,
        world: &DebugDb,
        ty: &Type,
    ) -> Result<Self, LoadError<M::Error>> {
        let Type::CEnum(s) = ty else { return Err(LoadError::NotACEnum) };

        let disc_value = load_unsigned(
            world.endian(),
            machine,
            addr,
            usize::try_from(s.byte_size).unwrap(),
        )?.ok_or(LoadError::DataUnavailable)?;

        let e = s
            .enumerators
            .get(&disc_value)
            .ok_or(LoadError::BadDiscriminator(disc_value))?;

        Ok(Self {
            name: s.name.clone(),
            disc: e.name.clone(),
        })
    }
}

#[derive(Clone, Debug)]
pub struct Pointer {
    pub name: String,
    pub dest_type_id: TypeId,
    pub value: u64,
}

impl Pointer {
    fn is_probably_mut(&self) -> bool {
        self.name.starts_with("&mut") || self.name.starts_with("*mut") || self.name.starts_with("*_")
    }
}

impl Load for Pointer {
    fn from_state<M: Machine>(
        machine: &M,
        addr: u64,
        world: &DebugDb,
        ty: &Type,
    ) -> Result<Self, LoadError<M::Error>> {
        // TODO support pointer sizes

        let Type::Pointer(s) = ty else { return Err(LoadError::NotAPointer); };

        let value = load_unsigned(world.endian(),  machine, addr, world.pointer_size())?
            .ok_or(LoadError::DataUnavailable)?;

        Ok(Self {
            name: Cow::into_owned(ty.name(world)),
            dest_type_id: s.type_id,
            value,
        })
    }
}
