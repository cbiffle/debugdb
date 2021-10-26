pub mod value;
pub mod load;

use std::collections::{BTreeMap, BTreeSet};
use object::{Object, ObjectSection};
use std::borrow::Cow;
use indexmap::IndexMap;

/// A database of types extracted from the debug info of a program.
///
/// This is primarily focused on correctly representing Rust types, but it can
/// represent a large subset of C types as a side effect -- currently only
/// unnamed types present a problem. This could be fixed.
#[derive(Clone, Debug, Default)]
pub struct Types {
    /// Endianness of the target system.
    endian: gimli::RunTimeEndian,
    /// Pointer width of the target system. Currently only 32 and 64 are
    /// supported here.
    is_64: bool,

    /// All types in the program, indexed by location in the debug section(s).
    ///
    /// This is the authoritative set of types, other type-related fields index
    /// into this.
    ///
    /// Invariant: within each entry, the key is the same as the type's `offset`
    /// field.
    types: BTreeMap<gimli::UnitSectionOffset, Type>,

    /// Index: type name to location(s) that can be looked up in `types`.
    ///
    /// Invariant: all string keys correspond to names of types in `types`.
    ///
    /// Invariant: all UnitSectionOffset values have corresponding entries in
    /// `types`.
    type_name_index: BTreeMap<String, BTreeSet<gimli::UnitSectionOffset>>,
}

impl Types {
    /// Gets the endianness of the program.
    pub fn endian(&self) -> gimli::RunTimeEndian {
        self.endian
    }

    /// Gets the size of a pointer in the program, in bytes.
    pub fn pointer_size(&self) -> u64 {
        if self.is_64 {
            8
        } else {
            4
        }
    }

    /// Produces an iterator over all types defined in the program, together
    /// with their unique section offsets.
    pub fn types(&self) -> impl Iterator<Item = (gimli::UnitSectionOffset, &Type)> + '_ {
        self.types.iter()
            .map(|(&goff, ty)| (goff, ty))
    }

    /// Looks up the type corresponding to a unique section offset. If the
    /// offset was found inside another type in `self`, our consistency rules
    /// guarantee that this will return `Some`, so it can be unwrapped.
    ///
    /// If you've gotten `goff` from somewhere else, you may or may not find a
    /// type.
    pub fn type_from_goff(&self, goff: gimli::UnitSectionOffset) -> Option<&Type> {
        self.types.get(&goff)
    }

    /// Shorthand for looking up the name of a type by unique section offset.
    ///
    /// If the offset was found inside another type in `self`, our consistency
    /// rules guarantee that this will return `Some`.
    pub fn name_from_goff(&self, goff: gimli::UnitSectionOffset) -> Option<Cow<'_, str>> {
        Some(self.type_from_goff(goff)?.name(self))
    }

    /// Consults the type-name index and returns an iterator over types with a
    /// given name.
    ///
    /// Names are matched in their entirety, e.g. the name `"Option"` does not
    /// match a type `"core::option::Option<u16>"`.
    pub fn types_by_name(&self, name: &str) -> impl Iterator<Item = (gimli::UnitSectionOffset, &Type)> + '_ {
        self.type_name_index.get(name)
            .into_iter()
            .flat_map(move |set| set.iter()
                .map(move |&goff| (goff, &self.types[&goff])))
    }
}


#[derive(Clone, Debug)]
pub struct TypesBuilder {
    path: Vec<String>,
    endian: gimli::RunTimeEndian,
    is_64: bool,
    types: BTreeMap<gimli::UnitSectionOffset, Type>,
}

impl TypesBuilder {
    pub fn new(endian: gimli::RunTimeEndian, is_64: bool) -> Self {
        Self {
            endian,
            path: vec![],
            is_64,
            types: BTreeMap::new(),
        }
    }

    pub fn record_type(&mut self, t: impl Into<Type>) {
        let t = t.into();
        self.types.insert(t.offset(), t);
    }

    pub fn format_path(&self, name: impl std::fmt::Display) -> String {
        if self.path.is_empty() {
            name.to_string()
        } else {
            format!("{}::{}", self.path.join("::"), name)
        }
    }

    pub fn path_component<T>(&mut self, c: impl Into<String>, body: impl FnOnce(&mut Self) -> T) -> T {
        self.path.push(c.into());
        let result = body(self);
        self.path.pop();
        result
    }

    pub fn build(self) -> Result<Types, Box<dyn std::error::Error>> {
        let check = |goff| -> Result<(), Box<dyn std::error::Error>> {
            if self.types.contains_key(&goff) {
                Ok(())
            } else {
                Err(format!("reference to missing type {:x?}", goff).into())
            }
        };
        // Validate that the world is complete and internally consistent.
        for t in self.types.values() {
            match t {
                Type::Base(_) => (),
                Type::CEnum(_) => (),

                Type::Struct(s) => {
                    for ttp in &s.template_type_parameters {
                        check(ttp.ty_goff.into())?;
                    }
                    for m in s.members.values() {
                        check(m.ty_goff.into())?;
                    }
                }
                Type::Union(s) => {
                    for ttp in &s.template_type_parameters {
                        check(ttp.ty_goff.into())?;
                    }
                    for m in &s.members {
                        check(m.ty_goff.into())?;
                    }
                }
                Type::Enum(s) => {
                    for ttp in &s.template_type_parameters {
                        check(ttp.ty_goff.into())?;
                    }
                    match &s.variant_part.shape {
                        VariantShape::Zero => (),
                        VariantShape::One(variant) => {
                            check(variant.member.ty_goff)?;
                        }
                        VariantShape::Many { member, variants, .. } => {
                            check(member.ty_goff)?;
                            for v in variants.values() {
                                check(v.member.ty_goff)?;
                            }
                        }
                    }
                }
                Type::Array(s) => {
                    check(s.element_ty_goff.into())?;
                    // The index type is synthetic, but, might as well.
                    check(s.index_ty_goff.into())?;
                }
                Type::Pointer(s) => {
                    check(s.ty_goff.into())?;
                }
                Type::Subroutine(s) => {
                    if let Some(t) = s.return_ty_goff {
                        check(t.into())?;
                    }
                    for &t in &s.formal_parameters {
                        check(t.into())?;
                    }
                }
            }
        }

        // Build type name index. We only index types with inherent names, i.e.
        // not arrays or subroutines.
        let type_name_index = index_by_key(
            &self.types,
            |_, t| match t {
                Type::Struct(s) => Some(s.name.clone()),
                Type::Enum(s) => Some(s.name.clone()),
                Type::Base(s) => Some(s.name.clone()),
                Type::CEnum(s) => Some(s.name.clone()),
                Type::Union(s) => Some(s.name.clone()),
                Type::Pointer(s) => Some(s.name.clone()),
                _ => None,
            },
        );
        Ok(Types {
            endian: self.endian,
            types: self.types,
            is_64: self.is_64,
            type_name_index,
        })
    }
}

/// Utility for indexing entries in a key-value table by some projection.
///
/// `table` is a sequence of keys and values in arbitrary order.
///
/// `project` takes a key-value pair and produces some datum to be indexed.
///
/// The result is a mapping from the data produced by `project` to keys in
/// `table`.
fn index_by_key<'t, K: 't, V: 't, T>(
    table: impl IntoIterator<Item = (&'t K, &'t V)>,
    mut project: impl FnMut(&K, &V) -> Option<T>,
) -> BTreeMap<T, BTreeSet<K>>
where T: Ord,
      K: Ord + Clone,
{
    let mut index: BTreeMap<T, BTreeSet<K>> = BTreeMap::new();

    for (k, v) in table {
        if let Some(i) = project(k, v) {
            index.entry(i)
                .or_default()
                .insert(k.clone());
        }
    }

    index
}

pub fn parse_file<'a>(object: &'a object::File) -> Result<Types, Box<dyn std::error::Error>> {
    let endian = if object.is_little_endian() {
        gimli::RunTimeEndian::Little
    } else {
        gimli::RunTimeEndian::Big
    };

    let load_section = |id: gimli::SectionId| -> Result<Cow<'a, [u8]>, gimli::Error> {
        match object.section_by_name(id.name()) {
            Some(section) => Ok(section
                .uncompressed_data()
                .unwrap_or(Default::default())),
            None => Ok(Default::default()),
        }
    };

    let dwarf_cow = gimli::Dwarf::load(&load_section)?;

    let dwarf = dwarf_cow.borrow(|section| gimli::EndianSlice::new(section, endian));

    let mut iter = dwarf.units();
    let mut builder = TypesBuilder::new(endian, object.is_64());

    while let Some(header) = iter.next()? {
        let unit = dwarf.unit(header)?;

        let mut entries = unit.entries();
        while let Some(()) = entries.next_entry()? {
            if entries.current().is_none() {
                break;
            }
            parse_entry(
                &dwarf,
                &unit,
                &mut entries,
                &mut builder,
            )?;
        }
    }

    builder.build()
}

fn handle_nested_types(
    dwarf: &gimli::Dwarf<gimli::EndianSlice<gimli::RunTimeEndian>>,
    unit: &gimli::Unit<gimli::EndianSlice<gimli::RunTimeEndian>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, gimli::EndianSlice<gimli::RunTimeEndian>>,
    builder: &mut TypesBuilder,
) -> Result<(), Box<dyn std::error::Error>> {
    if let Some(child) = cursor.current() {
        match child.tag() {
            gimli::constants::DW_TAG_base_type => {
                parse_base_type(dwarf, unit, cursor, builder)?;
            }
            gimli::constants::DW_TAG_structure_type => {
                parse_structure_type(dwarf, unit, cursor, builder)?;
            }
            gimli::constants::DW_TAG_enumeration_type => {
                parse_enumeration_type(dwarf, unit, cursor, builder)?;
            }
            gimli::constants::DW_TAG_array_type => {
                parse_array_type(dwarf, unit, cursor, builder)?;
            }
            gimli::constants::DW_TAG_pointer_type => {
                parse_pointer_type(dwarf, unit, cursor, builder)?;
            }
            gimli::constants::DW_TAG_subroutine_type => {
                parse_subroutine_type(dwarf, unit, cursor, builder)?;
            }
            gimli::constants::DW_TAG_union_type => {
                parse_union_type(dwarf, unit, cursor, builder)?;
            }
            gimli::constants::DW_TAG_namespace => {
                parse_namespace(dwarf, unit, cursor, builder)?;
            }
            _ => {
                skip_entry(cursor)?;
            }
        }
    }

    Ok(())
}

fn parse_entry(
    dwarf: &gimli::Dwarf<gimli::EndianSlice<gimli::RunTimeEndian>>,
    unit: &gimli::Unit<gimli::EndianSlice<gimli::RunTimeEndian>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, gimli::EndianSlice<gimli::RunTimeEndian>>,
    builder: &mut TypesBuilder,
) -> Result<(), Box<dyn std::error::Error>> {
    let entry = cursor.current().unwrap();

    let mut attrs = entry.attrs();
    while let Some(_) = attrs.next()? {
        // discard
    }

    if entry.has_children() {
        while let Some(()) = cursor.next_entry()? {
            if let Some(_) = cursor.current() {
                handle_nested_types(dwarf, unit, cursor, builder)?;
            } else {
                break;
            }
        }
    }

    Ok(())
}

fn parse_namespace(
    dwarf: &gimli::Dwarf<gimli::EndianSlice<gimli::RunTimeEndian>>,
    unit: &gimli::Unit<gimli::EndianSlice<gimli::RunTimeEndian>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, gimli::EndianSlice<gimli::RunTimeEndian>>,
    builder: &mut TypesBuilder,
) -> Result<(), Box<dyn std::error::Error>> {
    let entry = cursor.current().unwrap();
    assert!(entry.tag() == gimli::constants::DW_TAG_namespace);
    let mut name = None;

    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::constants::DW_AT_name => {
                name = Some(get_attr_string(dwarf, attr.value())?);
            }
            _ => (),
        }
    }

    let name = name.unwrap();

    if entry.has_children() {
        builder.path_component(name, |builder| {
            while let Some(()) = cursor.next_entry()? {
                if let Some(_) = cursor.current() {
                    handle_nested_types(dwarf, unit, cursor, builder)?;
                } else {
                    break;
                }

            }
            Ok(())
        })
    } else {
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub struct Base {
    pub name: String,
    pub encoding: Encoding,
    pub byte_size: u64,
    pub offset: gimli::UnitSectionOffset<usize>,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Encoding {
    Unsigned,
    Signed,
    UnsignedChar,
    SignedChar,
    Boolean,
    Float,
    ComplexFloat,
}

fn parse_base_type(
    dwarf: &gimli::Dwarf<gimli::EndianSlice<gimli::RunTimeEndian>>,
    unit: &gimli::Unit<gimli::EndianSlice<gimli::RunTimeEndian>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, gimli::EndianSlice<gimli::RunTimeEndian>>,
    builder: &mut TypesBuilder,
) -> Result<(), Box<dyn std::error::Error>> {
    let entry = cursor.current().unwrap();
    assert!(entry.tag() == gimli::constants::DW_TAG_base_type);

    let offset = entry.offset().to_unit_section_offset(unit);
    let mut name = None;
    let mut byte_size = None;
    let mut encoding = None;

    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::constants::DW_AT_name => {
                name = Some(get_attr_string(dwarf, attr.value())?);
            }
            gimli::constants::DW_AT_byte_size => {
                byte_size = Some(attr.value().udata_value().unwrap());
            }
            gimli::constants::DW_AT_encoding => {
                if let gimli::AttributeValue::Encoding(e) = attr.value() {
                    encoding = Some(match e {
                        gimli::constants::DW_ATE_unsigned => Encoding::Unsigned,
                        gimli::constants::DW_ATE_signed => Encoding::Signed,
                        gimli::constants::DW_ATE_boolean => Encoding::Boolean,
                        gimli::constants::DW_ATE_unsigned_char => Encoding::UnsignedChar,
                        gimli::constants::DW_ATE_signed_char => Encoding::SignedChar,
                        gimli::constants::DW_ATE_float => Encoding::Float,
                        gimli::constants::DW_ATE_complex_float => Encoding::ComplexFloat,
                        _ => panic!("unsupported encoding: {:?}", e),
                    });
                } else {
                    panic!("unexpected value for encoding: {:?}", attr.value());
                }
            }
            _ => (),
        }
    }

    let name = name.unwrap().into_owned();
    let byte_size = byte_size.unwrap();
    let encoding = encoding.unwrap();

    builder.record_type(Base {
        name,
        offset,
        encoding,
        byte_size,
    });
    Ok(())
}

#[derive(Debug, Clone)]
pub struct Struct {
    pub name: String,
    pub byte_size: u64,
    pub alignment: Option<u64>,
    pub template_type_parameters: Vec<TemplateTypeParameter>,
    pub tuple_like: bool,
    pub members: IndexMap<String, Member>,
    pub offset: gimli::UnitSectionOffset<usize>,
}

#[derive(Debug, Clone)]
pub struct Enum {
    pub name: String,
    pub byte_size: u64,
    pub alignment: Option<u64>,
    pub template_type_parameters: Vec<TemplateTypeParameter>,
    pub variant_part: VariantPart,
    pub offset: gimli::UnitSectionOffset<usize>,
}

#[derive(Debug, Clone)]
pub enum Type {
    Struct(Struct),
    Enum(Enum),
    Base(Base),
    CEnum(CEnum),
    Array(Array),
    Pointer(Pointer),
    Union(Union),
    Subroutine(Subroutine),
}

impl Type {
    pub fn offset(&self) -> gimli::UnitSectionOffset<usize> {
        // TODO so this field should clearly get factored out....
        match self {
            Self::Struct(s) => s.offset,
            Self::Enum(s) => s.offset,
            Self::Base(s) => s.offset,
            Self::CEnum(s) => s.offset,
            Self::Array(s) => s.offset,
            Self::Pointer(s) => s.offset,
            Self::Union(s) => s.offset,
            Self::Subroutine(s) => s.offset,
        }
    }

    pub fn alignment(&self, world: &Types) -> Option<u64> {
        match self {
            Self::Struct(s) => s.alignment,
            Self::Enum(s) => s.alignment,
            Self::Base(s) => {
                // TODO: we're going to just assume that all base types are
                // naturally aligned.
                Some(s.byte_size)
            },
            Self::CEnum(s) => Some(s.alignment),
            Self::Union(s) => Some(s.alignment),
            Self::Array(a) => {
                let eltty = world.type_from_goff(a.element_ty_goff.into())?;
                eltty.alignment(world)
            }
            Self::Pointer(_) => Some(world.pointer_size()),
            Self::Subroutine(_)=> None,
        }
    }

    pub fn byte_size(&self, world: &Types) -> Option<u64> {
        match self {
            Self::Struct(s) => Some(s.byte_size),
            Self::Enum(s) => Some(s.byte_size),
            Self::Base(s) => Some(s.byte_size),
            Self::CEnum(s) => Some(s.byte_size),
            Self::Union(s) => Some(s.byte_size),
            Self::Array(a) => {
                let eltty = world.type_from_goff(a.element_ty_goff.into())?;
                let eltsize = eltty.byte_size(world)?;
                Some(a.count? * eltsize)
            }
            Self::Pointer(_) => Some(world.pointer_size()),
            Self::Subroutine(_)=> None,
        }
    }

    pub fn name(&self, world: &Types) -> Cow<'_, str> {
        match self {
            Self::Struct(s) => (&s.name).into(),
            Self::Enum(s) => (&s.name).into(),
            Self::Base(s) => (&s.name).into(),
            Self::CEnum(s) => (&s.name).into(),
            Self::Union(s) => (&s.name).into(),
            Self::Pointer(s) => (&s.name).into(),
            Self::Array(a) => {
                let eltname = world.type_from_goff(a.element_ty_goff.into())
                    .map(|t| t.name(world))
                    .unwrap_or("???".into());

                if let Some(n) = a.count {
                    format!("[{}; {}]", eltname, n).into()
                } else {
                    format!("[{}; ???]", eltname).into()
                }
            },
            Self::Subroutine(_) => "subroutine".into(), // TODO
        }
    }
}

impl From<Base> for Type {
    fn from(x: Base) -> Self {
        Self::Base(x)
    }
}

impl From<Struct> for Type {
    fn from(x: Struct) -> Self {
        Self::Struct(x)
    }
}

impl From<Enum> for Type {
    fn from(x: Enum) -> Self {
        Self::Enum(x)
    }
}

impl From<Union> for Type {
    fn from(x: Union) -> Self {
        Self::Union(x)
    }
}

impl From<Pointer> for Type {
    fn from(x: Pointer) -> Self {
        Self::Pointer(x)
    }
}

impl From<Array> for Type {
    fn from(x: Array) -> Self {
        Self::Array(x)
    }
}

impl From<CEnum> for Type {
    fn from(x: CEnum) -> Self {
        Self::CEnum(x)
    }
}

impl From<Subroutine> for Type {
    fn from(x: Subroutine) -> Self {
        Self::Subroutine(x)
    }
}

fn parse_structure_type(
    dwarf: &gimli::Dwarf<gimli::EndianSlice<gimli::RunTimeEndian>>,
    unit: &gimli::Unit<gimli::EndianSlice<gimli::RunTimeEndian>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, gimli::EndianSlice<gimli::RunTimeEndian>>,
    builder: &mut TypesBuilder,
) -> Result<(), Box<dyn std::error::Error>> {
    let entry = cursor.current().unwrap();
    assert!(entry.tag() == gimli::constants::DW_TAG_structure_type);

    let offset = entry.offset().to_unit_section_offset(unit);
    let mut name = None;
    let mut byte_size = None;
    let mut alignment = None;

    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::constants::DW_AT_name => {
                name = Some(get_attr_string(dwarf, attr.value())?);
            }
            gimli::constants::DW_AT_byte_size => {
                byte_size = Some(attr.value().udata_value().unwrap());
            }
            gimli::constants::DW_AT_alignment => {
                alignment = Some(attr.value().udata_value().unwrap());
            }
            gimli::constants::DW_AT_declaration => {
                skip_entry(cursor)?;
                return Ok(());
            }
            _ => (),
        }
    }

    let mut template_type_parameters = vec![];
    let mut members = IndexMap::default();
    let mut variant_parts = vec![];

    let name = name.unwrap();
    if entry.has_children() {
        builder.path_component(name.clone(), |builder| {
            while let Some(()) = cursor.next_entry()? {
                if let Some(child) = cursor.current() {
                    match child.tag() {
                        gimli::constants::DW_TAG_template_type_parameter => {
                            template_type_parameters.push(
                                parse_template_type_parameter(dwarf, unit, cursor)?
                            );
                        }
                        gimli::constants::DW_TAG_member => {
                            let m = parse_member(dwarf, unit, cursor)?;
                            if let Some(n) = &m.name {
                                if let Some(old_m) = members.insert(n.clone(), m) {
                                    panic!("duplicate member for name {:?}", old_m.name);
                                }
                            } else {
                                panic!("nameless member confuse author");
                            }
                        }
                        gimli::constants::DW_TAG_variant_part => {
                            variant_parts.push(
                                parse_variant_part(dwarf, unit, cursor)?
                            );
                        }
                        _ => {
                            handle_nested_types(dwarf, unit, cursor, builder)?;
                        }
                    }
                } else {
                    break;
                }

            }
            Ok::<_, Box<dyn std::error::Error>>(())
        })?;
    }

    let byte_size = byte_size.unwrap();
    let name = builder.format_path(name);
    if variant_parts.is_empty() {
        // Scan members to see if this looks like a tuple -- either a raw tuple
        // or a tuple struct.
        let tuple_like = members.values().enumerate().all(|(i, m)| {
            if let Some(name) = &m.name {
                if name.starts_with("__") {
                    if let Ok(n) = name[2..].parse::<usize>() {
                        return n == i;
                    }
                }
            }
            false
        });
        builder.record_type(Struct {
            name,
            byte_size,
            alignment,
            template_type_parameters,
            offset,
            members,
            tuple_like,
        });
    } else if variant_parts.len() == 1 {
        assert!(members.is_empty(), "expected no members next to variant part, found {}", members.len());
        let variant_part = variant_parts.into_iter().next().unwrap();
        builder.record_type(Enum {
            name,
            byte_size,
            alignment,
            template_type_parameters,
            offset,
            variant_part,
        });
    } else {
        panic!("expected 1 variant part at most, found {}", variant_parts.len());
    }
    Ok(())
}

#[derive(Debug, Clone)]
pub struct TemplateTypeParameter {
    pub name: String,
    pub ty_goff: gimli::UnitSectionOffset,
}

fn parse_template_type_parameter(
    dwarf: &gimli::Dwarf<gimli::EndianSlice<gimli::RunTimeEndian>>,
    unit: &gimli::Unit<gimli::EndianSlice<gimli::RunTimeEndian>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, gimli::EndianSlice<gimli::RunTimeEndian>>,
) -> Result<TemplateTypeParameter, Box<dyn std::error::Error>> {
    let entry = cursor.current().unwrap();
    assert!(entry.tag() == gimli::constants::DW_TAG_template_type_parameter);

    let mut ty_goff = None;
    let mut name = None;

    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::constants::DW_AT_name => {
                name = Some(get_attr_string(dwarf, attr.value())?);
            }
            gimli::constants::DW_AT_type => {
                if let gimli::AttributeValue::UnitRef(o) = attr.value() {
                    ty_goff = Some(o.to_unit_section_offset(&unit));
                } else if let gimli::AttributeValue::DebugInfoRef(o) = attr.value() {
                    ty_goff = Some(o.into());
                } else {
                    panic!("unexpected type type: {:?}", attr.value());
                }
            }
            _ => (),
        }
    }

    let (name, ty_goff) = (name.unwrap(), ty_goff.unwrap());
    let name = name.to_string();

    Ok(TemplateTypeParameter { name, ty_goff })
}

#[derive(Debug, Clone)]
pub struct Member {
    pub name: Option<String>,
    pub artificial: bool,
    pub ty_goff: gimli::UnitSectionOffset,
    pub alignment: Option<u64>,
    pub location: u64,
    pub offset: gimli::UnitSectionOffset<usize>,
}

fn parse_member(
    dwarf: &gimli::Dwarf<gimli::EndianSlice<gimli::RunTimeEndian>>,
    unit: &gimli::Unit<gimli::EndianSlice<gimli::RunTimeEndian>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, gimli::EndianSlice<gimli::RunTimeEndian>>,
) -> Result<Member, Box<dyn std::error::Error>> {
    let entry = cursor.current().unwrap();
    assert!(entry.tag() == gimli::constants::DW_TAG_member);

    let mut name = None;
    let mut ty_goff = None;
    let mut alignment = None;
    let mut location = None;
    let mut artificial = false;

    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::constants::DW_AT_name => {
                name = Some(get_attr_string(dwarf, attr.value())?);
            }
            gimli::constants::DW_AT_artificial => {
                match attr.value() {
                    gimli::AttributeValue::Flag(f) => {
                        artificial = f;
                    }
                    v => panic!("unexpected artificial value: {:?}", v),
                }
            }
            gimli::constants::DW_AT_type => {
                if let gimli::AttributeValue::UnitRef(o) = attr.value() {
                    ty_goff = Some(o.to_unit_section_offset(&unit));
                } else if let gimli::AttributeValue::DebugInfoRef(o) = attr.value() {
                    ty_goff = Some(o.into());
                } else {
                    panic!("unexpected type type: {:?}", attr.value());
                }
            }
            gimli::constants::DW_AT_alignment => {
                alignment = Some(attr.value().udata_value().unwrap());
            }
            gimli::constants::DW_AT_data_member_location => {
                location = Some(attr.value().udata_value().unwrap());
            }
            _ => (),
        }
    }

    let offset = entry.offset().to_unit_section_offset(unit);
    let ty_goff = ty_goff.unwrap();
    let location = location.unwrap();
    let name = name.map(|s| s.to_string());

    Ok(Member {
        name,
        artificial,
        ty_goff,
        alignment,
        location,
        offset,
    })
}

#[derive(Debug, Clone)]
pub struct VariantPart {
    pub offset: gimli::UnitSectionOffset<usize>,
    pub shape: VariantShape,
}

#[derive(Debug, Clone)]
pub enum VariantShape {
    Zero,
    One(Variant),
    Many {
        discr: gimli::UnitSectionOffset<usize>,
        member: Member,
        variants: IndexMap<Option<u64>, Variant>,
    },
}

fn parse_variant_part(
    dwarf: &gimli::Dwarf<gimli::EndianSlice<gimli::RunTimeEndian>>,
    unit: &gimli::Unit<gimli::EndianSlice<gimli::RunTimeEndian>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, gimli::EndianSlice<gimli::RunTimeEndian>>,
) -> Result<VariantPart, Box<dyn std::error::Error>> {
    let entry = cursor.current().unwrap();
    assert!(entry.tag() == gimli::constants::DW_TAG_variant_part);

    let offset = entry.offset().to_unit_section_offset(unit);
    let mut discr = None;

    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::constants::DW_AT_discr => {
                if let gimli::AttributeValue::UnitRef(o) = attr.value() {
                    discr = Some(o.to_unit_section_offset(&unit));
                } else {
                    panic!("unexpected discr type: {:?}", attr.value());
                }
            }
            _ => (),
        }
    }

    let mut members = vec![];
    let mut variants = IndexMap::default();
    if entry.has_children() {
        while let Some(()) = cursor.next_entry()? {
            if let Some(child) = cursor.current() {
                match child.tag() {
                    gimli::constants::DW_TAG_member => {
                        members.push(
                            parse_member(dwarf, unit, cursor)?
                        );
                    }
                    gimli::constants::DW_TAG_variant => {
                        let (discr_value, v) = parse_variant(dwarf, unit, cursor)?;
                        variants.insert(discr_value, v);
                    }
                    _ => {
                        skip_entry(cursor)?;
                    }
                }
            } else {
                break;
            }
        }
    }

    if members.len() > 1 {
        panic!("Variant parts are expected to have a single member; this one has {}", members.len());
    }

    let shape = if variants.len() == 0 {
        VariantShape::Zero
    } else if variants.len() == 1 {

        if let Some(d) = variants.keys().next().unwrap() {
            VariantShape::Many {
                discr: discr.unwrap(),
                member: members.into_iter().next().unwrap(),
                variants,
            }
        } else {
            let (_d, v) = variants.into_iter().next().unwrap();
            VariantShape::One(v)
        }
    } else {
        VariantShape::Many {
            discr: discr.unwrap(),
            member: members.into_iter().next().unwrap(),
            variants,
        }
    };
    Ok(VariantPart {
        shape,
        offset,
    })
}

#[derive(Debug, Clone)]
pub struct Variant {
    pub member: Member,
    pub offset: gimli::UnitSectionOffset<usize>,
}

fn parse_variant(
    dwarf: &gimli::Dwarf<gimli::EndianSlice<gimli::RunTimeEndian>>,
    unit: &gimli::Unit<gimli::EndianSlice<gimli::RunTimeEndian>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, gimli::EndianSlice<gimli::RunTimeEndian>>,
) -> Result<(Option<u64>, Variant), Box<dyn std::error::Error>> {
    let entry = cursor.current().unwrap();
    assert!(entry.tag() == gimli::constants::DW_TAG_variant);

    let offset = entry.offset().to_unit_section_offset(unit);
    let mut discr_value = None;

    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::constants::DW_AT_discr_value => {
                discr_value = Some(attr.value().udata_value().unwrap());
            }
            _ => (),
        }
    }

    let mut members = vec![];
    if entry.has_children() {
        while let Some(()) = cursor.next_entry()? {
            if let Some(child) = cursor.current() {
                match child.tag() {
                    gimli::constants::DW_TAG_member => {
                        members.push(
                            parse_member(dwarf, unit, cursor)?
                        );
                    }
                    _ => {
                        skip_entry(cursor)?;
                    }
                }
            } else {
                break;
            }
        }
    }

    if members.len() > 1 {
        panic!("Variants are expected to have a single member; this one has {}", members.len());
    }
    let member = members.into_iter().next().unwrap();

    Ok((discr_value, Variant { member, offset }))
}

#[derive(Debug, Clone)]
pub struct CEnum {
    pub name: String,
    pub enum_class: bool,
    pub byte_size: u64,
    pub alignment: u64,
    pub enumerators: IndexMap<u64, Enumerator>,
    pub offset: gimli::UnitSectionOffset<usize>,
}

#[derive(Debug, Clone)]
pub struct Enumerator {
    pub name: String,
    pub const_value: u64,
    pub offset: gimli::UnitSectionOffset<usize>,
}

fn parse_enumeration_type(
    dwarf: &gimli::Dwarf<gimli::EndianSlice<gimli::RunTimeEndian>>,
    unit: &gimli::Unit<gimli::EndianSlice<gimli::RunTimeEndian>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, gimli::EndianSlice<gimli::RunTimeEndian>>,
    builder: &mut TypesBuilder,
) -> Result<(), Box<dyn std::error::Error>> {
    let entry = cursor.current().unwrap();
    assert!(entry.tag() == gimli::constants::DW_TAG_enumeration_type);

    let offset = entry.offset().to_unit_section_offset(unit);
    let mut name = None;
    let mut byte_size = None;
    let mut alignment = None;
    let mut enum_class = false;

    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::constants::DW_AT_name => {
                name = Some(get_attr_string(dwarf, attr.value())?);
            }
            gimli::constants::DW_AT_byte_size => {
                byte_size = Some(attr.value().udata_value().unwrap());
            }
            gimli::constants::DW_AT_alignment => {
                alignment = Some(attr.value().udata_value().unwrap());
            }
            gimli::constants::DW_AT_enum_class => {
                enum_class = attr.value() == gimli::AttributeValue::Flag(true);
            }
            _ => (),
        }
    }

    let mut enumerators = IndexMap::default();

    let name = name.unwrap();
    if entry.has_children() {
        builder.path_component(name.clone(), |_| {
            while let Some(()) = cursor.next_entry()? {
                if let Some(child) = cursor.current() {
                    match child.tag() {
                        gimli::constants::DW_TAG_enumerator => {
                            let e = parse_enumerator(dwarf, unit, cursor)?;
                            enumerators.insert(e.const_value, e);
                        }
                        _ => {
                            skip_entry(cursor)?;
                        }
                    }
                } else {
                    break;
                }

            }
            Ok::<_, Box<dyn std::error::Error>>(())
        })?;
    }

    let (byte_size, alignment) = (byte_size.unwrap(), alignment.unwrap());
    let name = builder.format_path(name);

    builder.record_type(CEnum {
        name,
        offset,
        enum_class,
        byte_size,
        alignment,
        enumerators,
    });
    Ok(())
}

fn parse_enumerator(
    dwarf: &gimli::Dwarf<gimli::EndianSlice<gimli::RunTimeEndian>>,
    unit: &gimli::Unit<gimli::EndianSlice<gimli::RunTimeEndian>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, gimli::EndianSlice<gimli::RunTimeEndian>>,
) -> Result<Enumerator, Box<dyn std::error::Error>> {
    let entry = cursor.current().unwrap();
    assert!(entry.tag() == gimli::constants::DW_TAG_enumerator);

    let mut name = None;
    let mut const_value = None;

    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::constants::DW_AT_name => {
                name = Some(get_attr_string(dwarf, attr.value())?);
            }
            gimli::constants::DW_AT_const_value => {
                const_value = Some(attr.value().udata_value()
                    .or_else(|| attr.value().sdata_value().map(|x| x as u64))
                    .unwrap());
            }
            _ => (),
        }
    }

    let name = name.unwrap().into_owned();
    let const_value = const_value.unwrap();

    Ok(Enumerator {
        name,
        const_value,
        offset: entry.offset().to_unit_section_offset(unit),
    })
}

#[derive(Debug, Clone)]
pub struct Array {
    pub element_ty_goff: gimli::UnitSectionOffset,
    pub index_ty_goff: gimli::UnitSectionOffset,
    pub lower_bound: u64,
    pub count: Option<u64>,
    pub offset: gimli::UnitSectionOffset<usize>,
}

fn parse_array_type(
    dwarf: &gimli::Dwarf<gimli::EndianSlice<gimli::RunTimeEndian>>,
    unit: &gimli::Unit<gimli::EndianSlice<gimli::RunTimeEndian>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, gimli::EndianSlice<gimli::RunTimeEndian>>,
    builder: &mut TypesBuilder,
) -> Result<(), Box<dyn std::error::Error>> {
    let entry = cursor.current().unwrap();
    assert!(entry.tag() == gimli::constants::DW_TAG_array_type);

    let offset = entry.offset().to_unit_section_offset(unit);
    let mut element_ty_goff = None;

    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::constants::DW_AT_type => {
                if let gimli::AttributeValue::UnitRef(o) = attr.value() {
                    element_ty_goff = Some(o.to_unit_section_offset(&unit));
                } else if let gimli::AttributeValue::DebugInfoRef(o) = attr.value() {
                    element_ty_goff = Some(o.into());
                } else {
                    panic!("unexpected type type: {:?}", attr.value());
                }
            }
            _ => (),
        }
    }

    let element_ty_goff = element_ty_goff.unwrap();

    let mut subrange = None;
    if entry.has_children() {
        while let Some(()) = cursor.next_entry()? {
            if let Some(child) = cursor.current() {
                match child.tag() {
                    gimli::constants::DW_TAG_subrange_type => {
                        subrange = Some(parse_subrange_type(dwarf, unit, cursor)?);
                    }
                    _ => {
                        skip_entry(cursor)?;
                    }
                }
            } else {
                break;
            }

        }
    }
    let (index_ty_goff, lower_bound, count) = subrange.unwrap();

    builder.record_type(Array {
        element_ty_goff,
        index_ty_goff,
        lower_bound,
        count,
        offset,
    });
    Ok(())
}

fn parse_subrange_type(
    _dwarf: &gimli::Dwarf<gimli::EndianSlice<gimli::RunTimeEndian>>,
    unit: &gimli::Unit<gimli::EndianSlice<gimli::RunTimeEndian>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, gimli::EndianSlice<gimli::RunTimeEndian>>,
) -> Result<(gimli::UnitSectionOffset, u64, Option<u64>), Box<dyn std::error::Error>> {
    let entry = cursor.current().unwrap();
    assert!(entry.tag() == gimli::constants::DW_TAG_subrange_type);

    let mut ty_goff = None;
    let mut lower_bound = None;
    let mut count = None;

    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::constants::DW_AT_type => {
                if let gimli::AttributeValue::UnitRef(o) = attr.value() {
                    ty_goff = Some(o.to_unit_section_offset(&unit));
                } else if let gimli::AttributeValue::DebugInfoRef(o) = attr.value() {
                    ty_goff = Some(o.into());
                } else {
                    panic!("unexpected type type: {:?}", attr.value());
                }
            }
            gimli::constants::DW_AT_lower_bound => {
                lower_bound = Some(attr.value().udata_value().unwrap());
            },
            gimli::constants::DW_AT_count => {
                count = Some(attr.value().udata_value().unwrap());
            },
            _ => (),
        }
    }

    let offset = entry.offset().to_unit_section_offset(unit);
    let ty_goff = ty_goff.unwrap();
    let lower_bound = lower_bound.unwrap_or(0);

    if entry.has_children() {
        while let Some(()) = cursor.next_entry()? {
            if let Some(child) = cursor.current() {
                match child.tag() {
                    _ => {
                        skip_entry(cursor)?;
                    }
                }
            } else {
                break;
            }

        }
    }
    Ok((ty_goff, lower_bound, count))
}

#[derive(Debug, Clone)]
pub struct Pointer {
    pub ty_goff: gimli::UnitSectionOffset,
    pub name: String,
    pub offset: gimli::UnitSectionOffset<usize>,
}

fn parse_pointer_type(
    dwarf: &gimli::Dwarf<gimli::EndianSlice<gimli::RunTimeEndian>>,
    unit: &gimli::Unit<gimli::EndianSlice<gimli::RunTimeEndian>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, gimli::EndianSlice<gimli::RunTimeEndian>>,
    builder: &mut TypesBuilder,
) -> Result<(), Box<dyn std::error::Error>> {
    let entry = cursor.current().unwrap();
    assert!(entry.tag() == gimli::constants::DW_TAG_pointer_type);

    let offset = entry.offset().to_unit_section_offset(unit);
    let mut name = None;
    let mut ty_goff = None;

    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::constants::DW_AT_name => {
                name = Some(get_attr_string(dwarf, attr.value())?);
            }
            gimli::constants::DW_AT_type => {
                if let gimli::AttributeValue::UnitRef(o) = attr.value() {
                    ty_goff = Some(o.to_unit_section_offset(&unit));
                } else if let gimli::AttributeValue::DebugInfoRef(o) = attr.value() {
                    ty_goff = Some(o.into());
                } else {
                    panic!("unexpected type type: {:?}", attr.value());
                }
            }
            gimli::constants::DW_AT_declaration => {
                skip_entry(cursor)?;
                return Ok(());
            }
            _ => (),
        }
    }

    if name.is_none() || ty_goff.is_none() {
        eprintln!("uh weird {:x?}", offset);
        return Ok(());
    }

    let name = name.unwrap().into_owned();
    let ty_goff = ty_goff.unwrap();

    if entry.has_children() {
        while let Some(()) = cursor.next_entry()? {
            if let Some(child) = cursor.current() {
                match child.tag() {
                    _ => {
                        skip_entry(cursor)?;
                    }
                }
            } else {
                break;
            }

        }
    }

    builder.record_type(Pointer {
        ty_goff,
        name,
        offset,
    });
    Ok(())
}

#[derive(Debug, Clone)]
pub struct Union {
    pub name: String,
    pub byte_size: u64,
    pub alignment: u64,
    pub template_type_parameters: Vec<TemplateTypeParameter>,
    pub members: Vec<Member>,
    pub offset: gimli::UnitSectionOffset<usize>,
}

fn parse_union_type(
    dwarf: &gimli::Dwarf<gimli::EndianSlice<gimli::RunTimeEndian>>,
    unit: &gimli::Unit<gimli::EndianSlice<gimli::RunTimeEndian>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, gimli::EndianSlice<gimli::RunTimeEndian>>,
    builder: &mut TypesBuilder,
) -> Result<(), Box<dyn std::error::Error>> {
    let entry = cursor.current().unwrap();
    assert!(entry.tag() == gimli::constants::DW_TAG_union_type);

    let offset = entry.offset().to_unit_section_offset(unit);
    let mut name = None;
    let mut byte_size = None;
    let mut alignment = None;

    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::constants::DW_AT_name => {
                name = Some(get_attr_string(dwarf, attr.value())?);
            }
            gimli::constants::DW_AT_byte_size => {
                byte_size = Some(attr.value().udata_value().unwrap());
            }
            gimli::constants::DW_AT_alignment => {
                alignment = Some(attr.value().udata_value().unwrap());
            }
            gimli::constants::DW_AT_declaration => {
                skip_entry(cursor)?;
                return Ok(());
            }
            _ => (),
        }
    }

    let mut template_type_parameters = vec![];
    let mut members = vec![];

    let name = name.unwrap();
    if entry.has_children() {
        builder.path_component(name.clone(), |_| {
            while let Some(()) = cursor.next_entry()? {
                if let Some(child) = cursor.current() {
                    match child.tag() {
                        gimli::constants::DW_TAG_template_type_parameter => {
                            template_type_parameters.push(
                                parse_template_type_parameter(dwarf, unit, cursor)?
                            );
                        }
                        gimli::constants::DW_TAG_member => {
                            members.push(
                                parse_member(dwarf, unit, cursor)?
                            );
                        }
                        _ => {
                            skip_entry(cursor)?;
                        }
                    }
                } else {
                    break;
                }
            }
            Ok::<_, Box<dyn std::error::Error>>(())
        })?;
    }

    let (byte_size, alignment) = (byte_size.unwrap(), alignment.unwrap());
    let name = builder.format_path(name);
    builder.record_type(Union {
        name,
        byte_size,
        alignment,
        template_type_parameters,
        offset,
        members,
    });
    Ok(())
}

#[derive(Clone, Debug)]
pub struct Subroutine {
    pub return_ty_goff: Option<gimli::UnitSectionOffset>,
    pub formal_parameters: Vec<gimli::UnitSectionOffset>,
    pub offset: gimli::UnitSectionOffset<usize>,
}

fn parse_subroutine_type(
    dwarf: &gimli::Dwarf<gimli::EndianSlice<gimli::RunTimeEndian>>,
    unit: &gimli::Unit<gimli::EndianSlice<gimli::RunTimeEndian>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, gimli::EndianSlice<gimli::RunTimeEndian>>,
    builder: &mut TypesBuilder,
) -> Result<(), Box<dyn std::error::Error>> {
    let entry = cursor.current().unwrap();
    assert!(entry.tag() == gimli::constants::DW_TAG_subroutine_type);

    let offset = entry.offset().to_unit_section_offset(unit);
    let mut return_ty_goff = None;

    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::constants::DW_AT_type => {
                if let gimli::AttributeValue::UnitRef(o) = attr.value() {
                    return_ty_goff = Some(o.to_unit_section_offset(&unit));
                } else if let gimli::AttributeValue::DebugInfoRef(o) = attr.value() {
                    return_ty_goff = Some(o.into());
                } else {
                    panic!("unexpected type type: {:?}", attr.value());
                }
            }
            _ => (),
        }
    }

    let mut formal_parameters = vec![];

    if entry.has_children() {
        while let Some(()) = cursor.next_entry()? {
            if let Some(child) = cursor.current() {
                match child.tag() {
                    gimli::constants::DW_TAG_formal_parameter => {
                        formal_parameters.push(
                            parse_formal_parameter(dwarf, unit, cursor)?
                        );
                    }
                    _ => {
                        skip_entry(cursor)?;
                    }
                }
            } else {
                break;
            }
        }
    }

    builder.record_type(Subroutine {
        return_ty_goff,
        formal_parameters,
        offset,
    });
    Ok(())
}

fn parse_formal_parameter(
    _dwarf: &gimli::Dwarf<gimli::EndianSlice<gimli::RunTimeEndian>>,
    unit: &gimli::Unit<gimli::EndianSlice<gimli::RunTimeEndian>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, gimli::EndianSlice<gimli::RunTimeEndian>>,
) -> Result<gimli::UnitSectionOffset, Box<dyn std::error::Error>> {
    let entry = cursor.current().unwrap();
    assert!(entry.tag() == gimli::constants::DW_TAG_formal_parameter);

    let mut ty_goff = None;

    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::constants::DW_AT_type => {
                if let gimli::AttributeValue::UnitRef(o) = attr.value() {
                    ty_goff = Some(o.to_unit_section_offset(&unit));
                } else if let gimli::AttributeValue::DebugInfoRef(o) = attr.value() {
                    ty_goff = Some(o.into());
                } else {
                    panic!("unexpected type type: {:?}", attr.value());
                }
            }
            _ => (),
        }
    }

    let ty_goff = ty_goff.unwrap();

    Ok(ty_goff)
}


fn get_attr_string<'a>(
    dwarf: &'a gimli::Dwarf<gimli::EndianSlice<gimli::RunTimeEndian>>,
    attrval: gimli::AttributeValue<gimli::EndianSlice<gimli::RunTimeEndian>>,
) -> Result<Cow<'a, str>, Box<dyn std::error::Error>> {
    match attrval {
        gimli::AttributeValue::DebugStrRef(offset) => {
            if let Ok(s) = dwarf.debug_str.get_str(offset) {
                Ok(s.to_string_lossy())
            } else {
                Ok(format!("<.debug_str+0x{:08x}>", offset.0).into())
            }
        }
        gimli::AttributeValue::String(data) => {
            Ok(data.to_string_lossy().into_owned().into()) // TODO hack
        }
        _ => {
            Err(format!("expected string, got: {:?}", attrval).into())
        }
    }
}

fn skip_entry(
    cursor: &mut gimli::EntriesCursor<'_, '_, gimli::EndianSlice<gimli::RunTimeEndian>>,
) -> Result<(), Box<dyn std::error::Error>> {
    let entry = cursor.current().unwrap();

    match entry.tag() {
        gimli::constants::DW_TAG_structure_type => {
            eprintln!("WARN: structure skipped");
        },
        gimli::constants::DW_TAG_enumeration_type => {
            eprintln!("WARN: enumeration skipped");
        },
        _ => (),
    }

    if entry.has_children() {
        while let Some(()) = cursor.next_entry()? {
            if let Some(_) = cursor.current() {
                skip_entry(cursor)?;
            } else {
                break;
            }
        }
    }

    Ok(())
}
