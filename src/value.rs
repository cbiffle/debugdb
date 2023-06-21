//! Abstract, dynamic, JSON-like representation of Rust values.
//!
//! This can be read from a program image using `Load` even if the program doing
//! the reading doesn't know the type shape in advance.

use crate::load::{choose_variant, load_unsigned, Load};
use crate::{Encoding, Type, DebugDb, TypeId};
use std::borrow::Cow;
use std::collections::BTreeMap;
use std::convert::TryFrom;

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
            }
        }
        None
    }
}

impl Load for Value {
    fn from_buffer(
        buffer: &[u8],
        addr: usize,
        world: &DebugDb,
        ty: &Type,
    ) -> Result<Self, Box<dyn std::error::Error>> {
        match ty {
            Type::Base(_) => {
                Ok(Self::Base(Base::from_buffer(buffer, addr, world, ty)?))
            }
            Type::Array(_) => {
                Ok(Self::Array(Vec::from_buffer(buffer, addr, world, ty)?))
            }
            Type::Struct(_) => {
                Ok(Self::Struct(Struct::from_buffer(buffer, addr, world, ty)?))
            }
            Type::CEnum(_) => {
                Ok(Self::CEnum(CEnum::from_buffer(buffer, addr, world, ty)?))
            }
            Type::Enum(_) => {
                Ok(Self::Enum(Enum::from_buffer(buffer, addr, world, ty)?))
            }
            Type::Pointer(_) => Ok(Self::Pointer(Pointer::from_buffer(
                buffer, addr, world, ty,
            )?)),
            _ => unimplemented!(),
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub enum Base {
    U8(u8),
}

impl Load for Base {
    fn from_buffer(
        buffer: &[u8],
        addr: usize,
        _world: &DebugDb,
        ty: &Type,
    ) -> Result<Self, Box<dyn std::error::Error>> {
        if let Type::Base(b) = ty {
            match (b.encoding, b.byte_size) {
                (Encoding::Unsigned, 1) => Ok(Base::U8(buffer[addr])),
                _ => return Err("bad encoding/size".into()),
            }
        } else {
            Err("bad type".into())
        }
    }
}

#[derive(Clone, Debug)]
pub struct Struct {
    name: String,
    members: BTreeMap<String, Value>,
}

impl Load for Struct {
    fn from_buffer(
        buffer: &[u8],
        addr: usize,
        world: &DebugDb,
        ty: &Type,
    ) -> Result<Self, Box<dyn std::error::Error>> {
        if let Type::Struct(s) = ty {
            let mut members = BTreeMap::new();

            for m in &s.members {
                if let Some(n) = &m.name {
                    let t = world.type_by_id(m.type_id).unwrap();
                    let ma = addr + usize::try_from(m.location).unwrap();
                    let v = Value::from_buffer(buffer, ma, world, t)?;
                    members.insert(n.clone(), v);
                }
            }

            Ok(Self {
                name: s.name.clone(),
                members,
            })
        } else {
            Err("bad type".into())
        }
    }
}

#[derive(Clone, Debug)]
pub struct Enum {
    name: String,
    disc: String,
    value: Struct,
}

impl Load for Enum {
    fn from_buffer(
        buffer: &[u8],
        addr: usize,
        world: &DebugDb,
        ty: &Type,
    ) -> Result<Self, Box<dyn std::error::Error>> {
        if let Type::Enum(s) = ty {
            let v = choose_variant(buffer, addr, world, s)?;

            let vtype_id = v.member.type_id;
            let vty = world.type_by_id(vtype_id).unwrap();
            let va = addr + usize::try_from(v.member.location)?;
            let value = Struct::from_buffer(buffer, va, world, vty)?;

            Ok(Self {
                name: s.name.clone(),
                disc: v.member.name.as_ref().unwrap().clone(),
                value,
            })
        } else {
            Err("bad type".into())
        }
    }
}

#[derive(Clone, Debug)]
pub struct CEnum {
    name: String,
    disc: String,
}

impl Load for CEnum {
    fn from_buffer(
        buffer: &[u8],
        addr: usize,
        world: &DebugDb,
        ty: &Type,
    ) -> Result<Self, Box<dyn std::error::Error>> {
        if let Type::CEnum(s) = ty {
            let disc_value = load_unsigned(
                world.endian(),
                buffer,
                addr,
                usize::try_from(s.byte_size).unwrap(),
            );

            let e = s
                .enumerators
                .get(&disc_value)
                .ok_or("discriminator not valid for c-enum")?;

            Ok(Self {
                name: s.name.clone(),
                disc: e.name.clone(),
            })
        } else {
            Err("bad type".into())
        }
    }
}

#[derive(Clone, Debug)]
pub struct Pointer {
    name: String,
    dest_type_id: TypeId,
    value: u64,
}

impl Load for Pointer {
    fn from_buffer(
        buffer: &[u8],
        addr: usize,
        world: &DebugDb,
        ty: &Type,
    ) -> Result<Self, Box<dyn std::error::Error>> {
        // TODO support pointer sizes

        if let Type::Pointer(s) = ty {
            let value = load_unsigned(world.endian(), buffer, addr, 8);

            Ok(Self {
                name: Cow::into_owned(ty.name(world)),
                dest_type_id: s.type_id,
                value,
            })
        } else {
            Err("bad type".into())
        }
    }
}
