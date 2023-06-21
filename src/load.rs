//! Support for extracting values from a program image, processing them using
//! debug information, and turning them into Rust values in the observing
//! program.

use crate::{Encoding, Enum, Type, DebugDb, Variant, VariantShape};
use gimli::Reader;
use std::convert::TryFrom;

pub trait Load: Sized {
    fn from_buffer(
        buffer: &[u8],
        addr: usize,
        world: &DebugDb,
        ty: &Type,
    ) -> Result<Self, Box<dyn std::error::Error>>;
}

impl<A: Load, B: Load> Load for (A, B) {
    fn from_buffer(
        buffer: &[u8],
        addr: usize,
        world: &DebugDb,
        ty: &Type,
    ) -> Result<Self, Box<dyn std::error::Error>> {
        if let Type::Struct(s) = ty {
            if s.tuple_like {
                let m0 = s.unique_member("__0").ok_or("missing __0")?;
                let m0ty = world.type_by_id(m0.type_id).unwrap();
                let m1 = s.unique_member("__1").ok_or("missing __1")?;
                let m1ty = world.type_by_id(m1.type_id).unwrap();
                Ok((
                    A::from_buffer(
                        buffer,
                        addr + usize::try_from(m0.location).unwrap(),
                        world,
                        m0ty,
                    )?,
                    B::from_buffer(
                        buffer,
                        addr + usize::try_from(m1.location).unwrap(),
                        world,
                        m1ty,
                    )?,
                ))
            } else {
                Err("struct had wrong shape".into())
            }
        } else {
            Err("bad type".into())
        }
    }
}

impl Load for u8 {
    fn from_buffer(
        buffer: &[u8],
        addr: usize,
        _world: &DebugDb,
        ty: &Type,
    ) -> Result<u8, Box<dyn std::error::Error>> {
        if let Type::Base(b) = ty {
            if b.encoding != Encoding::Unsigned {
                return Err("bad encoding".into());
            }
            if b.byte_size != 1 {
                return Err("bad size".into());
            }
            Ok(buffer[addr])
        } else {
            Err("bad type".into())
        }
    }
}

impl Load for i8 {
    fn from_buffer(
        buffer: &[u8],
        addr: usize,
        _world: &DebugDb,
        ty: &Type,
    ) -> Result<Self, Box<dyn std::error::Error>> {
        if let Type::Base(b) = ty {
            if b.encoding != Encoding::Unsigned {
                return Err("bad encoding".into());
            }
            if b.byte_size != 1 {
                return Err("bad size".into());
            }
            Ok(buffer[addr] as i8)
        } else {
            Err("bad type".into())
        }
    }
}

macro_rules! base_impl {
    ($t:ty, $enc:ident, $read:ident) => {
        impl Load for $t {
            fn from_buffer(
                buffer: &[u8],
                addr: usize,
                world: &DebugDb,
                ty: &Type,
            ) -> Result<Self, Box<dyn std::error::Error>> {
                if let Type::Base(b) = ty {
                    if b.encoding != Encoding::$enc {
                        return Err("bad encoding".into());
                    }
                    if usize::try_from(b.byte_size).unwrap()
                        != std::mem::size_of::<Self>()
                    {
                        return Err("bad size".into());
                    }
                    Ok(gimli::EndianSlice::new(&buffer[addr..], world.endian())
                        .$read()?)
                } else {
                    Err("bad type".into())
                }
            }
        }
    };
}

base_impl!(u16, Unsigned, read_u16);
base_impl!(u32, Unsigned, read_u32);
base_impl!(u64, Unsigned, read_u64);

base_impl!(i16, Signed, read_i16);
base_impl!(i32, Signed, read_i32);
base_impl!(i64, Signed, read_i64);

impl<T: Load> Load for Vec<T> {
    fn from_buffer(
        buffer: &[u8],
        addr: usize,
        world: &DebugDb,
        ty: &Type,
    ) -> Result<Self, Box<dyn std::error::Error>> {
        if let Type::Array(s) = ty {
            let count = s.count.ok_or("non-finite array type")?;
            if s.lower_bound != 0 {
                return Err(
                    "array with non-zero lower bound not supported".into()
                );
            }
            let elty = world.type_by_id(s.element_type_id).unwrap();

            let elt_size = elty
                .byte_size(world)
                .ok_or("non-Sized type can't be array element")?;
            let elt_size = elt_size.max(elty.alignment(world).unwrap_or(0));
            let ary_size = elt_size
                .checked_mul(count)
                .ok_or("array larger than memory")?;

            let elt_size = usize::try_from(elt_size)?;
            let ary_size = usize::try_from(ary_size)?;

            let sub = &buffer[addr..addr + ary_size];
            let mut elts = Vec::with_capacity(usize::try_from(count)?);
            for chunk in sub.chunks_exact(elt_size) {
                elts.push(T::from_buffer(chunk, 0, world, elty)?);
            }
            Ok(elts)
        } else {
            Err("bad type".into())
        }
    }
}

/// A `Load` impl for Option-shaped types.
///
/// This will work for any enum with two variants, where one is named None and
/// has no payload, and the other is named Some and has one field.
impl<T: Load> Load for Option<T> {
    fn from_buffer(
        buffer: &[u8],
        addr: usize,
        world: &DebugDb,
        ty: &Type,
    ) -> Result<Self, Box<dyn std::error::Error>> {
        if let Type::Enum(s) = ty {
            // Option-like enums have two variants.
            if let VariantShape::Many { variants, .. } = &s.shape {
                if variants.len() != 2 {
                    return Err("wrong enum shape for Option".into());
                }
                // Those variants are named None and Some.
                for v in variants.values() {
                    if let Some(n) = &v.member.name {
                        if n == "None" || n == "Some" {
                            continue;
                        }
                    }
                    return Err("wrong enum shape for Option".into());
                }
            }
            // Ok, that's the extend of the type validation I'm comfortable
            // doing here for performance reasons.

            let v = choose_variant(buffer, addr, world, s)?;
            let is_some = v.member.name.as_ref().unwrap() == "Some";
            let vty = world.type_by_id(v.member.type_id).unwrap();
            // Option-like enums have tuple variants.
            if let Type::Struct(s) = vty {
                if !s.tuple_like {
                    return Err("wrong enum shape for Option".into());
                }
                if is_some {
                    if s.members.len() == 1 {
                        let m = &s.members[0];
                        let mty =
                            world.type_by_id(m.type_id).unwrap();
                        let ma = addr + usize::try_from(m.location).unwrap();
                        Ok(Some(T::from_buffer(buffer, ma, world, mty)?))
                    } else {
                        return Err("wrong enum shape for Option".into());
                    }
                } else {
                    if s.members.is_empty() {
                        Ok(None)
                    } else {
                        return Err("wrong enum shape for Option".into());
                    }
                }
            } else {
                return Err("wrong enum shape for Option".into());
            }
        } else {
            Err("bad type".into())
        }
    }
}

pub(crate) fn choose_variant<'e>(
    buffer: &[u8],
    addr: usize,
    world: &'e DebugDb,
    e: &'e Enum,
) -> Result<&'e Variant, Box<dyn std::error::Error>> {
    match &e.shape {
        VariantShape::Zero => {
            return Err("load of uninhabited enum".into());
        }
        VariantShape::One(v) => Ok(v),
        VariantShape::Many {
            member, variants, ..
        } => {
            let dtype_id = member.type_id;
            let dty = world.type_by_id(dtype_id).unwrap();
            let da = addr + usize::try_from(member.location)?;
            let dsize = usize::try_from(dty.byte_size(world).unwrap()).unwrap();
            let d = load_unsigned(world.endian(), buffer, da, dsize);
            let v = variants
                .get(&Some(d))
                .or_else(|| variants.get(&None))
                .ok_or("discriminator not defined in type")?;
            Ok(v)
        }
    }
}

pub(crate) fn load_unsigned(
    endian: gimli::RunTimeEndian,
    buffer: &[u8],
    addr: usize,
    size: usize,
) -> u64 {
    let mut buffer = gimli::EndianSlice::new(&buffer[addr..], endian);
    match size {
        1 => u64::from(buffer.read_u8().unwrap()),
        2 => u64::from(buffer.read_u16().unwrap()),
        4 => u64::from(buffer.read_u32().unwrap()),
        8 => buffer.read_u64().unwrap(),
        _ => unimplemented!(),
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{TypeId, DebugDbBuilder};

    #[derive(Debug, Default)]
    struct OffsetMaker {
        next_offset: usize,
    }

    impl OffsetMaker {
        fn next(&mut self) -> gimli::UnitSectionOffset {
            let n = self.next_offset;
            self.next_offset += 1;
            gimli::DebugInfoOffset(n).into()
        }
    }

    fn make_option_u16(
        builder: &mut DebugDbBuilder,
        om: &mut OffsetMaker,
    ) -> TypeId {
        let u16_goff = om.next();
        builder.record_type(crate::Base {
            name: "u16".to_string(),
            encoding: Encoding::Unsigned,
            byte_size: 2,
            offset: u16_goff.into(),
        });

        let none_goff = om.next();
        builder.record_type(crate::Struct {
            name: "core::option::Option<u16>::None".to_string(),
            byte_size: 4,
            alignment: Some(2),
            offset: none_goff,
            tuple_like: true,
            template_type_parameters: vec![],
            members: indexmap::indexmap! {},
        });

        let some_goff = om.next();
        builder.record_type(crate::Struct {
            name: "core::option::Option<u16>::Some".to_string(),
            byte_size: 4,
            alignment: Some(2),
            offset: some_goff,
            tuple_like: true,
            template_type_parameters: vec![],
            members: indexmap::indexmap! {
                "__0".to_string() => crate::Member {
                    name: Some("__0".to_string()),
                    artificial: false,
                    alignment: Some(2),
                    location: 2,
                    offset: om.next(),
                    type_id: u16_goff.into(),
                },
            },
        });

        let option_goff = om.next();
        builder.record_type(crate::Enum {
            name: "core::option::Option<u16>".to_string(),
            byte_size: 4,
            alignment: Some(2),
            template_type_parameters: vec![],
            shape: VariantShape::Many {
                discr: om.next(),
                member: crate::Member {
                    name: None,
                    artificial: true,
                    type_id: u16_goff.into(),
                    alignment: Some(2),
                    location: 0,
                    offset: om.next(),
                },
                variants: indexmap::indexmap! {
                    Some(0) => crate::Variant {
                        offset: om.next(),
                        member: crate::Member {
                            name: Some("None".to_string()),
                            artificial: false,
                            alignment: Some(2),
                            location: 0,
                            type_id: none_goff.into(),
                            offset: om.next(),
                        },
                    },
                    Some(1) => crate::Variant {
                        offset: om.next(),
                        member: crate::Member {
                            name: Some("Some".to_string()),
                            artificial: false,
                            alignment: Some(2),
                            location: 0,
                            type_id: some_goff.into(),
                            offset: om.next(),
                        },
                    },
                },
            },
            offset: option_goff.into(),
        });

        option_goff.into()
    }

    #[test]
    fn load_option_u16() {
        let mut om = OffsetMaker::default();
        let mut builder =
            DebugDbBuilder::new(gimli::RunTimeEndian::Little, false);

        let option_goff = make_option_u16(&mut builder, &mut om);

        let world = builder.build().unwrap();
        let oty = world.type_by_id(option_goff).unwrap();

        let img = [0, 0, 0xAB, 0xCD];
        assert_eq!(
            Option::<u16>::from_buffer(&img, 0, &world, oty).unwrap(),
            None
        );
        let img = [1, 0, 0xAB, 0xCD];
        assert_eq!(
            Option::<u16>::from_buffer(&img, 0, &world, oty).unwrap(),
            Some(0xCDAB)
        );
    }

    #[test]
    fn load_u8_array() {
        let mut om = OffsetMaker::default();
        let mut builder =
            DebugDbBuilder::new(gimli::RunTimeEndian::Little, false);

        let u8_goff = om.next();
        builder.record_type(crate::Base {
            name: "u8".to_string(),
            encoding: Encoding::Unsigned,
            byte_size: 1,
            offset: u8_goff,
        });

        let index_type_goff = om.next();
        builder.record_type(crate::Base {
            name: "__ARRAY_INDEX_TYPE__".to_string(),
            encoding: Encoding::Unsigned,
            byte_size: 8,
            offset: index_type_goff,
        });

        let ary_goff = om.next();
        builder.record_type(crate::Array {
            element_type_id: TypeId(u8_goff),
            index_type_id: TypeId(index_type_goff),
            lower_bound: 0,
            count: Some(5),
            offset: ary_goff,
        });

        let world = builder.build().unwrap();
        let aty = world.type_by_id(TypeId(ary_goff)).unwrap();

        let img = [0, 1, 2, 3, 4];
        let ary: Vec<u8> = Load::from_buffer(&img, 0, &world, aty).unwrap();
        assert_eq!(ary, [0, 1, 2, 3, 4]);
    }
}
