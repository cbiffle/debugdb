//! Recursive descent parser for DWARF info (i.e. the part missing from Gimli).
//!
//! This consumes DWARF debug info sections by recursive descent, building up
//! our data model.

use crate::{DebugDbBuilder, Encoding, Base, Struct, Enum, Variant, VariantShape, TemplateTypeParameter, Member, TypeId, CEnum, Union, Enumerator, Array, Pointer, Subroutine, DeclCoord, Subprogram, SubParameter, InlinedSubroutine, StaticVariable};
use indexmap::IndexMap;
use std::borrow::Cow;
use std::num::NonZeroU64;

use gimli::constants as gim_con;

// Internal type abbreviations
type RtSlice<'a> = gimli::EndianSlice<'a, gimli::RunTimeEndian>;

pub fn parse_entry(
    dwarf: &gimli::Dwarf<RtSlice<'_>>,
    unit: &gimli::Unit<RtSlice<'_>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, RtSlice<'_>>,
    builder: &mut DebugDbBuilder,
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

/// Factored out of parsers for DWARF entities that can contain types. This
/// dispatches between the type or namespace parsing routines based on tag.
fn handle_nested_types(
    dwarf: &gimli::Dwarf<RtSlice<'_>>,
    unit: &gimli::Unit<RtSlice<'_>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, RtSlice<'_>>,
    builder: &mut DebugDbBuilder,
) -> Result<(), Box<dyn std::error::Error>> {
    if let Some(child) = cursor.current() {
        match child.tag() {
            gim_con::DW_TAG_base_type => {
                parse_base_type(dwarf, unit, cursor, builder)?;
            }
            gim_con::DW_TAG_structure_type => {
                parse_structure_type(dwarf, unit, cursor, builder)?;
            }
            gim_con::DW_TAG_enumeration_type => {
                parse_enumeration_type(dwarf, unit, cursor, builder)?;
            }
            gim_con::DW_TAG_array_type => {
                parse_array_type(dwarf, unit, cursor, builder)?;
            }
            gim_con::DW_TAG_pointer_type => {
                parse_pointer_type(dwarf, unit, cursor, builder)?;
            }
            gim_con::DW_TAG_subroutine_type => {
                parse_subroutine_type(dwarf, unit, cursor, builder)?;
            }
            gim_con::DW_TAG_union_type => {
                parse_union_type(dwarf, unit, cursor, builder)?;
            }
            gim_con::DW_TAG_namespace => {
                parse_namespace(dwarf, unit, cursor, builder)?;
            }
            gim_con::DW_TAG_subprogram => {
                parse_subprogram(dwarf, unit, cursor, builder)?;
            }
            gim_con::DW_TAG_variable => {
                parse_static_variable(dwarf, unit, cursor, builder)?;
            }
            _ => {
                skip_entry(cursor)?;
            }
        }
    }

    Ok(())
}

fn parse_namespace(
    dwarf: &gimli::Dwarf<RtSlice<'_>>,
    unit: &gimli::Unit<RtSlice<'_>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, RtSlice<'_>>,
    builder: &mut DebugDbBuilder,
) -> Result<(), Box<dyn std::error::Error>> {
    let entry = cursor.current().unwrap();
    assert!(entry.tag() == gim_con::DW_TAG_namespace);
    let mut name = None;

    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gim_con::DW_AT_name => {
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

fn parse_base_type(
    dwarf: &gimli::Dwarf<RtSlice<'_>>,
    unit: &gimli::Unit<RtSlice<'_>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, RtSlice<'_>>,
    builder: &mut DebugDbBuilder,
) -> Result<(), Box<dyn std::error::Error>> {
    let entry = cursor.current().unwrap();
    assert!(entry.tag() == gim_con::DW_TAG_base_type);

    let offset = entry.offset().to_unit_section_offset(unit);
    let mut name = None;
    let mut byte_size = None;
    let mut encoding = None;

    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gim_con::DW_AT_name => {
                name = Some(get_attr_string(dwarf, attr.value())?);
            }
            gim_con::DW_AT_byte_size => {
                byte_size = Some(attr.value().udata_value().unwrap());
            }
            gim_con::DW_AT_encoding => {
                if let gimli::AttributeValue::Encoding(e) = attr.value() {
                    encoding = Some(match e {
                        gim_con::DW_ATE_unsigned => Encoding::Unsigned,
                        gim_con::DW_ATE_signed => Encoding::Signed,
                        gim_con::DW_ATE_boolean => Encoding::Boolean,
                        gim_con::DW_ATE_unsigned_char => Encoding::UnsignedChar,
                        gim_con::DW_ATE_signed_char => Encoding::SignedChar,
                        gim_con::DW_ATE_float => Encoding::Float,
                        gim_con::DW_ATE_complex_float => Encoding::ComplexFloat,
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

fn parse_structure_type(
    dwarf: &gimli::Dwarf<RtSlice<'_>>,
    unit: &gimli::Unit<RtSlice<'_>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, RtSlice<'_>>,
    builder: &mut DebugDbBuilder,
) -> Result<(), Box<dyn std::error::Error>> {
    let entry = cursor.current().unwrap();
    assert!(entry.tag() == gim_con::DW_TAG_structure_type);

    let offset = entry.offset().to_unit_section_offset(unit);
    let mut name = None;
    let mut byte_size = None;
    let mut alignment = None;

    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gim_con::DW_AT_name => {
                name = Some(get_attr_string(dwarf, attr.value())?);
            }
            gim_con::DW_AT_byte_size => {
                byte_size = Some(attr.value().udata_value().unwrap());
            }
            gim_con::DW_AT_alignment => {
                alignment = Some(attr.value().udata_value().unwrap());
            }
            gim_con::DW_AT_declaration => {
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
                        gim_con::DW_TAG_template_type_parameter => {
                            template_type_parameters.push(
                                parse_template_type_parameter(
                                    dwarf, unit, cursor,
                                )?,
                            );
                        }
                        gim_con::DW_TAG_member => {
                            let m = parse_member(dwarf, unit, cursor)?;
                            if let Some(n) = &m.name {
                                if let Some(old_m) =
                                    members.insert(n.clone(), m)
                                {
                                    panic!(
                                        "duplicate member for name {:?}",
                                        old_m.name
                                    );
                                }
                            } else {
                                panic!("nameless member confuse author");
                            }
                        }
                        gim_con::DW_TAG_variant_part => {
                            variant_parts
                                .push(parse_variant_part(dwarf, unit, cursor)?);
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
        assert!(
            members.is_empty(),
            "expected no members next to variant part, found {}",
            members.len()
        );
        let shape = variant_parts.into_iter().next().unwrap();
        builder.record_type(Enum {
            name,
            byte_size,
            alignment,
            template_type_parameters,
            offset,
            shape,
        });
    } else {
        panic!(
            "expected 1 variant part at most, found {}",
            variant_parts.len()
        );
    }
    Ok(())
}

fn parse_template_type_parameter(
    dwarf: &gimli::Dwarf<RtSlice<'_>>,
    unit: &gimli::Unit<RtSlice<'_>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, RtSlice<'_>>,
) -> Result<TemplateTypeParameter, Box<dyn std::error::Error>> {
    let entry = cursor.current().unwrap();
    assert!(entry.tag() == gim_con::DW_TAG_template_type_parameter);

    let mut type_id = None;
    let mut name = None;

    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gim_con::DW_AT_name => {
                name = Some(get_attr_string(dwarf, attr.value())?);
            }
            gim_con::DW_AT_type => {
                if let gimli::AttributeValue::UnitRef(o) = attr.value() {
                    type_id = Some(o.to_unit_section_offset(&unit));
                } else if let gimli::AttributeValue::DebugInfoRef(o) =
                    attr.value()
                {
                    type_id = Some(o.into());
                } else {
                    panic!("unexpected type type: {:?}", attr.value());
                }
            }
            _ => (),
        }
    }

    let (name, type_id) = (name.unwrap(), TypeId(type_id.unwrap()));
    let name = name.to_string();

    Ok(TemplateTypeParameter { name, type_id })
}

fn parse_member(
    dwarf: &gimli::Dwarf<RtSlice<'_>>,
    unit: &gimli::Unit<RtSlice<'_>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, RtSlice<'_>>,
) -> Result<Member, Box<dyn std::error::Error>> {
    let entry = cursor.current().unwrap();
    assert!(entry.tag() == gim_con::DW_TAG_member);

    let mut name = None;
    let mut type_id = None;
    let mut alignment = None;
    let mut location = None;
    let mut artificial = false;

    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gim_con::DW_AT_name => {
                name = Some(get_attr_string(dwarf, attr.value())?);
            }
            gim_con::DW_AT_artificial => match attr.value() {
                gimli::AttributeValue::Flag(f) => {
                    artificial = f;
                }
                v => panic!("unexpected artificial value: {:?}", v),
            },
            gim_con::DW_AT_type => {
                if let gimli::AttributeValue::UnitRef(o) = attr.value() {
                    type_id = Some(o.to_unit_section_offset(&unit));
                } else if let gimli::AttributeValue::DebugInfoRef(o) =
                    attr.value()
                {
                    type_id = Some(o.into());
                } else {
                    panic!("unexpected type type: {:?}", attr.value());
                }
            }
            gim_con::DW_AT_alignment => {
                alignment = Some(attr.value().udata_value().unwrap());
            }
            gim_con::DW_AT_data_member_location => {
                location = Some(attr.value().udata_value().unwrap());
            }
            _ => (),
        }
    }

    let offset = entry.offset().to_unit_section_offset(unit);
    let type_id = TypeId(type_id.unwrap());
    let location = location.unwrap();
    let name = name.map(|s| s.to_string());

    Ok(Member {
        name,
        artificial,
        type_id,
        alignment,
        location,
        offset,
    })
}

fn parse_variant_part(
    dwarf: &gimli::Dwarf<RtSlice<'_>>,
    unit: &gimli::Unit<RtSlice<'_>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, RtSlice<'_>>,
) -> Result<VariantShape, Box<dyn std::error::Error>> {
    let entry = cursor.current().unwrap();
    assert!(entry.tag() == gim_con::DW_TAG_variant_part);

    let mut discr = None;

    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gim_con::DW_AT_discr => {
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
                    gim_con::DW_TAG_member => {
                        members.push(parse_member(dwarf, unit, cursor)?);
                    }
                    gim_con::DW_TAG_variant => {
                        let (discr_value, v) =
                            parse_variant(dwarf, unit, cursor)?;
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
        if variants.keys().next().unwrap().is_some() {
            // The single variant has a defined discriminator; use the Many
            // shape.
            VariantShape::Many {
                discr: discr.unwrap(),
                member: members.into_iter().next().unwrap(),
                variants,
            }
        } else {
            // The single variant has no discriminator.
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
    Ok(shape)
}

fn parse_variant(
    dwarf: &gimli::Dwarf<RtSlice<'_>>,
    unit: &gimli::Unit<RtSlice<'_>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, RtSlice<'_>>,
) -> Result<(Option<u64>, Variant), Box<dyn std::error::Error>> {
    let entry = cursor.current().unwrap();
    assert!(entry.tag() == gim_con::DW_TAG_variant);

    let offset = entry.offset().to_unit_section_offset(unit);
    let mut discr_value = None;

    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gim_con::DW_AT_discr_value => {
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
                    gim_con::DW_TAG_member => {
                        members.push(parse_member(dwarf, unit, cursor)?);
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
        panic!(
            "Variants are expected to have a single member; this one has {}",
            members.len()
        );
    }
    let member = members.into_iter().next().unwrap();

    Ok((discr_value, Variant { member, offset }))
}

fn parse_enumeration_type(
    dwarf: &gimli::Dwarf<RtSlice<'_>>,
    unit: &gimli::Unit<RtSlice<'_>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, RtSlice<'_>>,
    builder: &mut DebugDbBuilder,
) -> Result<(), Box<dyn std::error::Error>> {
    let entry = cursor.current().unwrap();
    assert!(entry.tag() == gim_con::DW_TAG_enumeration_type);

    let offset = entry.offset().to_unit_section_offset(unit);
    let mut name = None;
    let mut byte_size = None;
    let mut alignment = None;
    let mut enum_class = false;

    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gim_con::DW_AT_name => {
                name = Some(get_attr_string(dwarf, attr.value())?);
            }
            gim_con::DW_AT_byte_size => {
                byte_size = Some(attr.value().udata_value().unwrap());
            }
            gim_con::DW_AT_alignment => {
                alignment = Some(attr.value().udata_value().unwrap());
            }
            gim_con::DW_AT_enum_class => {
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
                        gim_con::DW_TAG_enumerator => {
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
    dwarf: &gimli::Dwarf<RtSlice<'_>>,
    unit: &gimli::Unit<RtSlice<'_>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, RtSlice<'_>>,
) -> Result<Enumerator, Box<dyn std::error::Error>> {
    let entry = cursor.current().unwrap();
    assert!(entry.tag() == gim_con::DW_TAG_enumerator);

    let mut name = None;
    let mut const_value = None;

    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gim_con::DW_AT_name => {
                name = Some(get_attr_string(dwarf, attr.value())?);
            }
            gim_con::DW_AT_const_value => {
                const_value = Some(
                    attr.value()
                        .udata_value()
                        .or_else(|| {
                            attr.value().sdata_value().map(|x| x as u64)
                        })
                        .unwrap(),
                );
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

fn parse_array_type(
    dwarf: &gimli::Dwarf<RtSlice<'_>>,
    unit: &gimli::Unit<RtSlice<'_>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, RtSlice<'_>>,
    builder: &mut DebugDbBuilder,
) -> Result<(), Box<dyn std::error::Error>> {
    let entry = cursor.current().unwrap();
    assert!(entry.tag() == gim_con::DW_TAG_array_type);

    let offset = entry.offset().to_unit_section_offset(unit);
    let mut element_type_id = None;

    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gim_con::DW_AT_type => {
                if let gimli::AttributeValue::UnitRef(o) = attr.value() {
                    element_type_id = Some(o.to_unit_section_offset(&unit));
                } else if let gimli::AttributeValue::DebugInfoRef(o) =
                    attr.value()
                {
                    element_type_id = Some(o.into());
                } else {
                    panic!("unexpected type type: {:?}", attr.value());
                }
            }
            _ => (),
        }
    }

    let element_type_id = TypeId(element_type_id.unwrap());

    let mut subrange = None;
    if entry.has_children() {
        while let Some(()) = cursor.next_entry()? {
            if let Some(child) = cursor.current() {
                match child.tag() {
                    gim_con::DW_TAG_subrange_type => {
                        subrange =
                            Some(parse_subrange_type(dwarf, unit, cursor)?);
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
    let (index_type_id, lower_bound, count) = subrange.unwrap();

    builder.record_type(Array {
        element_type_id,
        index_type_id,
        lower_bound,
        count,
        offset,
    });
    Ok(())
}

fn parse_subrange_type(
    _dwarf: &gimli::Dwarf<RtSlice<'_>>,
    unit: &gimli::Unit<RtSlice<'_>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, RtSlice<'_>>,
) -> Result<
    (TypeId, u64, Option<u64>),
    Box<dyn std::error::Error>,
> {
    let entry = cursor.current().unwrap();
    assert!(entry.tag() == gim_con::DW_TAG_subrange_type);

    let mut type_id = None;
    let mut lower_bound = None;
    let mut count = None;

    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gim_con::DW_AT_type => {
                if let gimli::AttributeValue::UnitRef(o) = attr.value() {
                    type_id = Some(o.to_unit_section_offset(&unit));
                } else if let gimli::AttributeValue::DebugInfoRef(o) =
                    attr.value()
                {
                    type_id = Some(o.into());
                } else {
                    panic!("unexpected type type: {:?}", attr.value());
                }
            }
            gim_con::DW_AT_lower_bound => {
                lower_bound = Some(attr.value().udata_value().unwrap());
            }
            gim_con::DW_AT_count => {
                count = Some(attr.value().udata_value().unwrap());
            }
            _ => (),
        }
    }

    let type_id = TypeId(type_id.unwrap());
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
    Ok((type_id, lower_bound, count))
}

fn parse_pointer_type(
    dwarf: &gimli::Dwarf<RtSlice<'_>>,
    unit: &gimli::Unit<RtSlice<'_>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, RtSlice<'_>>,
    builder: &mut DebugDbBuilder,
) -> Result<(), Box<dyn std::error::Error>> {
    let entry = cursor.current().unwrap();
    assert!(entry.tag() == gim_con::DW_TAG_pointer_type);

    let offset = entry.offset().to_unit_section_offset(unit);
    let mut name = None;
    let mut type_id = None;

    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gim_con::DW_AT_name => {
                name = Some(get_attr_string(dwarf, attr.value())?);
            }
            gim_con::DW_AT_type => {
                if let gimli::AttributeValue::UnitRef(o) = attr.value() {
                    type_id = Some(o.to_unit_section_offset(&unit));
                } else if let gimli::AttributeValue::DebugInfoRef(o) =
                    attr.value()
                {
                    type_id = Some(o.into());
                } else {
                    panic!("unexpected type type: {:?}", attr.value());
                }
            }
            gim_con::DW_AT_declaration => {
                skip_entry(cursor)?;
                return Ok(());
            }
            _ => (),
        }
    }

    if name.is_none() || type_id.is_none() {
        return Ok(());
    }

    let name = name.unwrap().into_owned();
    let type_id = TypeId(type_id.unwrap());

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
        type_id,
        name,
        offset,
    });
    Ok(())
}

fn parse_union_type(
    dwarf: &gimli::Dwarf<RtSlice<'_>>,
    unit: &gimli::Unit<RtSlice<'_>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, RtSlice<'_>>,
    builder: &mut DebugDbBuilder,
) -> Result<(), Box<dyn std::error::Error>> {
    let entry = cursor.current().unwrap();
    assert!(entry.tag() == gim_con::DW_TAG_union_type);

    let offset = entry.offset().to_unit_section_offset(unit);
    let mut name = None;
    let mut byte_size = None;
    let mut alignment = None;

    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gim_con::DW_AT_name => {
                name = Some(get_attr_string(dwarf, attr.value())?);
            }
            gim_con::DW_AT_byte_size => {
                byte_size = Some(attr.value().udata_value().unwrap());
            }
            gim_con::DW_AT_alignment => {
                alignment = Some(attr.value().udata_value().unwrap());
            }
            gim_con::DW_AT_declaration => {
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
                        gim_con::DW_TAG_template_type_parameter => {
                            template_type_parameters.push(
                                parse_template_type_parameter(
                                    dwarf, unit, cursor,
                                )?,
                            );
                        }
                        gim_con::DW_TAG_member => {
                            members.push(parse_member(dwarf, unit, cursor)?);
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

fn parse_subroutine_type(
    dwarf: &gimli::Dwarf<RtSlice<'_>>,
    unit: &gimli::Unit<RtSlice<'_>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, RtSlice<'_>>,
    builder: &mut DebugDbBuilder,
) -> Result<(), Box<dyn std::error::Error>> {
    let entry = cursor.current().unwrap();
    assert!(entry.tag() == gim_con::DW_TAG_subroutine_type);

    let offset = entry.offset().to_unit_section_offset(unit);
    let mut return_type_id = None;

    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gim_con::DW_AT_type => {
                if let gimli::AttributeValue::UnitRef(o) = attr.value() {
                    return_type_id = Some(TypeId(o.to_unit_section_offset(&unit)));
                } else if let gimli::AttributeValue::DebugInfoRef(o) =
                    attr.value()
                {
                    return_type_id = Some(TypeId(o.into()));
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
                    gim_con::DW_TAG_formal_parameter => {
                        formal_parameters
                            .push(parse_formal_parameter(dwarf, unit, cursor)?);
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
        return_type_id,
        formal_parameters,
        offset,
    });
    Ok(())
}

fn parse_formal_parameter(
    _dwarf: &gimli::Dwarf<RtSlice<'_>>,
    unit: &gimli::Unit<RtSlice<'_>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, RtSlice<'_>>,
) -> Result<TypeId, Box<dyn std::error::Error>> {
    let entry = cursor.current().unwrap();
    assert!(entry.tag() == gim_con::DW_TAG_formal_parameter);

    let mut type_id = None;

    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gim_con::DW_AT_type => {
                if let gimli::AttributeValue::UnitRef(o) = attr.value() {
                    type_id = Some(o.to_unit_section_offset(&unit));
                } else if let gimli::AttributeValue::DebugInfoRef(o) =
                    attr.value()
                {
                    type_id = Some(o.into());
                } else {
                    panic!("unexpected type type: {:?}", attr.value());
                }
            }
            _ => (),
        }
    }

    let type_id = TypeId(type_id.unwrap());

    Ok(type_id)
}

fn get_attr_string<'a>(
    dwarf: &'a gimli::Dwarf<RtSlice<'_>>,
    attrval: gimli::AttributeValue<RtSlice<'_>>,
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
        _ => Err(format!("expected string, got: {:?}", attrval).into()),
    }
}

fn skip_entry(
    cursor: &mut gimli::EntriesCursor<'_, '_, RtSlice<'_>>,
) -> Result<(), Box<dyn std::error::Error>> {
    let entry = cursor.current().unwrap();

    match entry.tag() {
        gim_con::DW_TAG_structure_type => {
            eprintln!("WARN: structure skipped: offset={:x?}",
                entry.offset());
        }
        gim_con::DW_TAG_enumeration_type => {
            eprintln!("WARN: enumeration skipped: offset={:x?}",
                entry.offset());
        }
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

fn parse_subprogram(
    dwarf: &gimli::Dwarf<RtSlice<'_>>,
    unit: &gimli::Unit<RtSlice<'_>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, RtSlice<'_>>,
    builder: &mut DebugDbBuilder,
) -> Result<(), Box<dyn std::error::Error>> {
    let entry = cursor.current().unwrap();
    assert!(entry.tag() == gim_con::DW_TAG_subprogram);
    let mut name = None;
    let mut linkage_name = None;
    let mut lo_pc = None;
    let mut hi_pc = None;
    let mut return_type_id = None;
    let mut decl_coord = DeclCoord::default();
    let mut abstract_origin = None;
    let mut noreturn = false;

    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gim_con::DW_AT_name => {
                name = Some(get_attr_string(dwarf, attr.value())?);
            }
            gim_con::DW_AT_linkage_name => {
                linkage_name = Some(get_attr_string(dwarf, attr.value())?.into_owned());
            }
            gim_con::DW_AT_noreturn => match attr.value() {
                gimli::AttributeValue::Flag(f) => {
                    noreturn = f;
                }
                v => panic!("unexpected noreturn value: {:?}", v),
            },
            gim_con::DW_AT_decl_file => {
                if let gimli::AttributeValue::FileIndex(f) = attr.value() {
                    if let Some(lp) = &unit.line_program {
                        if let Some(fent) = lp.header().file(f) {
                            let file = get_attr_string(dwarf, fent.path_name())?;
                            if let Some(dv) = fent.directory(lp.header()) {
                                decl_coord.file = Some(format!(
                                    "{}/{}",
                                    get_attr_string(dwarf, dv)?,
                                    file,
                                ));
                            } else {
                                decl_coord.file = Some(file.into_owned());
                            }
                        } else {
                            eprintln!("WARN: invalid file index");
                        }
                    } else {
                        eprintln!("WARN: missing line program");
                    }
                } else {
                    eprintln!("WARN: unexpected decl_file type: {:?}", attr.value());
                }
            }
            gim_con::DW_AT_decl_line => {
                decl_coord.line = NonZeroU64::new(attr.value().udata_value().unwrap());
            }
            gim_con::DW_AT_decl_column => {
                decl_coord.column = NonZeroU64::new(attr.value().udata_value().unwrap());
            }
            gim_con::DW_AT_low_pc => {
                if let gimli::AttributeValue::Addr(a) = attr.value() {
                    lo_pc = Some(a);
                } else {
                    eprintln!("WARN: unexpected low_pc type: {:?}", attr.value());
                }
            }
            gim_con::DW_AT_high_pc => {
                hi_pc = Some(attr.value().udata_value().unwrap());
            }
            gim_con::DW_AT_type => {
                if let gimli::AttributeValue::UnitRef(o) = attr.value() {
                    return_type_id = Some(TypeId(o.to_unit_section_offset(&unit)));
                } else if let gimli::AttributeValue::DebugInfoRef(o) =
                    attr.value()
                {
                    return_type_id = Some(TypeId(o.into()));
                } else {
                    panic!("unexpected type type: {:?}", attr.value());
                }
            }
            gim_con::DW_AT_abstract_origin => {
                if let gimli::AttributeValue::UnitRef(o) = attr.value() {
                    abstract_origin = Some(o.to_unit_section_offset(&unit));
                } else if let gimli::AttributeValue::DebugInfoRef(o) =
                    attr.value()
                {
                    abstract_origin = Some(o.into());
                } else {
                    panic!("unexpected abstract_origin type: {:?}", attr.value());
                }
            }
            // sibling
            // inline
            // prototyped
            // external
            // frame_base
            _ => {
                //println!("skipping subprogram attr: {:x?}", attr.name());
            }
        }
    }

    let pc_range = if let (Some(lo), Some(hi)) = (lo_pc, hi_pc) {
        Some(lo..lo + hi)
    } else {
        None
    };

    let offset = entry.offset().to_unit_section_offset(unit);

    let mut formal_parameters = vec![];
    let mut template_type_parameters = vec![];
    let mut inlines = vec![];
    if entry.has_children() {
        while let Some(()) = cursor.next_entry()? {
            if let Some(child) = cursor.current() {
                match child.tag() {
                    gim_con::DW_TAG_formal_parameter => {
                        formal_parameters
                            .push(parse_sub_parameter(dwarf, unit, cursor)?);
                    }
                    gim_con::DW_TAG_template_type_parameter => {
                        template_type_parameters.push(
                            parse_template_type_parameter(
                                dwarf, unit, cursor,
                            )?,
                        );
                    }
                    gim_con::DW_TAG_inlined_subroutine => {
                        inlines
                            .push(parse_inlined_subroutine(dwarf, unit, cursor)?);
                    }
                    // variable
                    // lexical_block
                    _ => {
                        //println!("skipping subprogram content: {:x?}", child.tag());
                        skip_entry(cursor)?;
                    }
                }
            } else {
                break;
            }
        }
    }

    let name = name.map(|s| builder.format_path(s));

    builder.record_subprogram(Subprogram {
        offset,
        name,
        pc_range,
        decl_coord,
        return_type_id,
        formal_parameters,
        template_type_parameters,
        inlines,
        abstract_origin,
        linkage_name,
        noreturn,
    });

    Ok(())
}

fn parse_sub_parameter(
    dwarf: &gimli::Dwarf<RtSlice<'_>>,
    unit: &gimli::Unit<RtSlice<'_>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, RtSlice<'_>>,
) -> Result<SubParameter, Box<dyn std::error::Error>> {
    let entry = cursor.current().unwrap();
    assert!(entry.tag() == gim_con::DW_TAG_formal_parameter);

    let mut type_id = None;
    let mut name = None;
    let mut decl_coord = DeclCoord::default();
    let mut abstract_origin = None;
    let mut const_value = None;

    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gim_con::DW_AT_name => {
                name = Some(get_attr_string(dwarf, attr.value())?.into_owned());
            }
            gim_con::DW_AT_type => {
                if let gimli::AttributeValue::UnitRef(o) = attr.value() {
                    type_id = Some(TypeId(o.to_unit_section_offset(&unit)));
                } else if let gimli::AttributeValue::DebugInfoRef(o) =
                    attr.value()
                {
                    type_id = Some(TypeId(o.into()));
                } else {
                    panic!("unexpected type type: {:?}", attr.value());
                }
            }
            gim_con::DW_AT_abstract_origin => {
                if let gimli::AttributeValue::UnitRef(o) = attr.value() {
                    abstract_origin = Some(o.to_unit_section_offset(&unit));
                } else if let gimli::AttributeValue::DebugInfoRef(o) =
                    attr.value()
                {
                    abstract_origin = Some(o.into());
                } else {
                    panic!("unexpected abstract_origin type: {:?}", attr.value());
                }
            }
            gim_con::DW_AT_decl_file => {
                if let gimli::AttributeValue::FileIndex(f) = attr.value() {
                    if let Some(lp) = &unit.line_program {
                        if let Some(fent) = lp.header().file(f) {
                            let file = get_attr_string(dwarf, fent.path_name())?;
                            if let Some(dv) = fent.directory(lp.header()) {
                                decl_coord.file = Some(format!(
                                    "{}/{}",
                                    get_attr_string(dwarf, dv)?,
                                    file,
                                ));
                            } else {
                                decl_coord.file = Some(file.into_owned());
                            }
                        } else {
                            eprintln!("WARN: invalid file index");
                        }
                    } else {
                        eprintln!("WARN: missing line program");
                    }
                } else {
                    eprintln!("WARN: unexpected decl_file type: {:?}", attr.value());
                }
            }
            gim_con::DW_AT_decl_line => {
                decl_coord.line = NonZeroU64::new(attr.value().udata_value().unwrap());
            }
            gim_con::DW_AT_decl_column => {
                decl_coord.column = NonZeroU64::new(attr.value().udata_value().unwrap());
            }
            gim_con::DW_AT_const_value => {
                const_value = Some(attr.value().udata_value().unwrap());
            }
            // location
            _ => {
                //println!("skipping subparam attr: {:x?}", attr.name());
            }
        }
    }

    let offset = entry.offset().to_unit_section_offset(unit);

    Ok(SubParameter {
        offset,
        name,
        decl_coord,
        type_id,
        abstract_origin,
        const_value,
    })
}

fn parse_inlined_subroutine(
    dwarf: &gimli::Dwarf<RtSlice<'_>>,
    unit: &gimli::Unit<RtSlice<'_>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, RtSlice<'_>>,
) -> Result<InlinedSubroutine, Box<dyn std::error::Error>> {
    let entry = cursor.current().unwrap();
    assert!(entry.tag() == gim_con::DW_TAG_inlined_subroutine);

    let mut abstract_origin = None;
    let mut call_coord = DeclCoord::default();
    let mut pc_ranges = vec![];
    let mut lo_pc = None;
    let mut hi_pc = None;

    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gim_con::DW_AT_ranges => {
                if let gimli::AttributeValue::RangeListsRef(roff) = attr.value() {
                    let roff = dwarf.ranges_offset_from_raw(unit, roff);
                    let mut riter = dwarf.ranges(unit, roff)?;
                    while let Some(range) = riter.next()? {
                        pc_ranges.push(range);
                    }
                } else {
                    eprintln!("WARN: unexpected ranges type: {:?}", attr.value());
                }
            }
            gim_con::DW_AT_call_file => {
                if let gimli::AttributeValue::FileIndex(f) = attr.value() {
                    if let Some(lp) = &unit.line_program {
                        if let Some(fent) = lp.header().file(f) {
                            let file = get_attr_string(dwarf, fent.path_name())?;
                            if let Some(dv) = fent.directory(lp.header()) {
                                call_coord.file = Some(format!(
                                    "{}/{}",
                                    get_attr_string(dwarf, dv)?,
                                    file,
                                ));
                            } else {
                                call_coord.file = Some(file.into_owned());
                            }
                        } else {
                            eprintln!("WARN: invalid file index");
                        }
                    } else {
                        eprintln!("WARN: missing line program");
                    }
                } else {
                    eprintln!("WARN: unexpected call_file type: {:?}", attr.value());
                }
            }
            gim_con::DW_AT_call_line => {
                call_coord.line = NonZeroU64::new(attr.value().udata_value().unwrap());
            }
            gim_con::DW_AT_call_column => {
                call_coord.column = NonZeroU64::new(attr.value().udata_value().unwrap());
            }
            gim_con::DW_AT_low_pc => {
                if let gimli::AttributeValue::Addr(a) = attr.value() {
                    lo_pc = Some(a);
                } else {
                    eprintln!("WARN: unexpected low_pc type: {:?}", attr.value());
                }
            }
            gim_con::DW_AT_high_pc => {
                hi_pc = Some(attr.value().udata_value().unwrap());
            }
            gim_con::DW_AT_abstract_origin => {
                if let gimli::AttributeValue::UnitRef(o) = attr.value() {
                    abstract_origin = Some(o.to_unit_section_offset(&unit));
                } else if let gimli::AttributeValue::DebugInfoRef(o) =
                    attr.value()
                {
                    abstract_origin = Some(o.into());
                } else {
                    panic!("unexpected abstract_origin type: {:?}", attr.value());
                }
            }
            _ => {
                //println!("skipping inlined subroutine attr: {:x?}", attr.name());
            }
        }
    }

    if let (Some(begin), Some(off)) = (lo_pc, hi_pc) {
        pc_ranges.push(gimli::Range {
            begin,
            end: begin + off,
        });
    }

    let offset = entry.offset().to_unit_section_offset(unit);

    let mut inlines = vec![];
    let mut formal_parameters = vec![];
    if entry.has_children() {
        while let Some(()) = cursor.next_entry()? {
            if let Some(child) = cursor.current() {
                match child.tag() {
                    gim_con::DW_TAG_inlined_subroutine => {
                        inlines
                            .push(parse_inlined_subroutine(dwarf, unit, cursor)?);
                    }
                    gim_con::DW_TAG_formal_parameter => {
                        formal_parameters
                            .push(parse_sub_parameter(dwarf, unit, cursor)?);
                    }
                    // lexical_block
                    _ => {
                        //println!("skipping subroutine content: {:x?}", child.tag());
                        skip_entry(cursor)?;
                    }
                }
            } else {
                break;
            }
        }
    }

    Ok(InlinedSubroutine {
        offset,
        pc_ranges,
        abstract_origin,
        call_coord,
        inlines,
        formal_parameters,
    })
}

fn parse_static_variable(
    dwarf: &gimli::Dwarf<RtSlice<'_>>,
    unit: &gimli::Unit<RtSlice<'_>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, RtSlice<'_>>,
    builder: &mut DebugDbBuilder,
) -> Result<(), Box<dyn std::error::Error>> {
    let entry = cursor.current().unwrap();
    assert!(entry.tag() == gim_con::DW_TAG_variable);

    let mut name = None;
    let mut linkage_name = None;
    let mut type_id = None;
    let mut decl = DeclCoord::default();
    let mut location = None;

    let offset = entry.offset().to_unit_section_offset(unit);

    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gim_con::DW_AT_name => {
                name = Some(get_attr_string(dwarf, attr.value())?);
            }
            gim_con::DW_AT_linkage_name => {
                linkage_name = Some(get_attr_string(dwarf, attr.value())?);
            }
            gim_con::DW_AT_location => {
                let e = attr.exprloc_value().unwrap();
                let mut eval = e.evaluation(unit.encoding());
                let mut result = eval.evaluate()?;
                loop {
                    match result {
                        gimli::EvaluationResult::Complete => {
                            let r = eval.result();
                            if r.len() == 1 {
                                match r[0].location {
                                    gimli::Location::Address { address } => {
                                        location = Some(address);
                                        break;
                                    }
                                    x => {
                                        panic!("unexpected static location: {:?}", x);
                                    }
                                }
                            } else {
                                panic!("unexpected eval results: {:?}", r);
                            }
                        }
                        gimli::EvaluationResult::RequiresRelocatedAddress(a) => {
                            result = eval.resume_with_relocated_address(a)?;

                        }
                        x => {
                            println!("unhandled location expression at {:x?}: {:?}", offset, x);
                            return Ok(())
                        }
                    } 
                }
            }
            gim_con::DW_AT_type => {
                if let gimli::AttributeValue::UnitRef(o) = attr.value() {
                    type_id = Some(o.to_unit_section_offset(&unit));
                } else if let gimli::AttributeValue::DebugInfoRef(o) =
                    attr.value()
                {
                    type_id = Some(o.into());
                } else {
                    panic!("unexpected type type: {:?}", attr.value());
                }
            }
            gim_con::DW_AT_decl_file => {
                if let gimli::AttributeValue::FileIndex(f) = attr.value() {
                    if let Some(lp) = &unit.line_program {
                        if let Some(fent) = lp.header().file(f) {
                            let file = get_attr_string(dwarf, fent.path_name())?;
                            if let Some(dv) = fent.directory(lp.header()) {
                                decl.file = Some(format!(
                                    "{}/{}",
                                    get_attr_string(dwarf, dv)?,
                                    file,
                                ));
                            } else {
                                decl.file = Some(file.into_owned());
                            }
                        } else {
                            eprintln!("WARN: invalid file index");
                        }
                    } else {
                        eprintln!("WARN: missing line program");
                    }
                } else {
                    eprintln!("WARN: unexpected call_file type: {:?}", attr.value());
                }
            }
            gim_con::DW_AT_decl_line => {
                decl.line = NonZeroU64::new(attr.value().udata_value().unwrap());
            }
            gim_con::DW_AT_decl_column => {
                decl.column = NonZeroU64::new(attr.value().udata_value().unwrap());
            }
            _ => {
                //println!("skipping static var attr: {:x?}", attr.name());
            }
        }
    }

    if location.is_none() {
        // skip!
        return Ok(());
    }

    let type_id = TypeId(type_id.unwrap());
    let location = location.unwrap();

    let name = if linkage_name.is_none() {
        // This is a heuristic for detecting #[no_mangle] Rust variables.
        name.unwrap().into_owned()
    } else {
        builder.format_path(name.unwrap())
    };


    builder.record_variable(StaticVariable {
        offset,
        name,
        type_id,
        decl,
        location,
    });
    Ok(())
}

