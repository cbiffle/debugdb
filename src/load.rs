//! Support for extracting values from a program image, processing them using
//! debug information, and turning them into Rust values in the observing
//! program.

use crate::{Encoding, Enum, Type, DebugDb, Variant, VariantShape};
use gimli::Endianity;
use rangemap::RangeInclusiveMap;
use thiserror::Error;
use std::convert::{TryFrom, Infallible};

pub trait Load: Sized {
    fn from_state<M: Machine>(
        machine: &M,
        addr: u64,
        world: &DebugDb,
        ty: &Type,
    ) -> Result<Self, LoadError<M::Error>>;
}

pub trait Machine {
    /// Error type that indicates that we had a failure to access machine state.
    type Error;
    /// Reads memory in the program's address space (or on a physically
    /// addressed system, _the_ address space) starting at `address`. Up to
    /// `dest.len()` bytes will be read, and copied into `dest` starting from
    /// the beginning.
    ///
    /// "Success" here means that access did not fail, so the rest of the output
    /// is valid. In this case, `read_memory` will return `Ok(n)`, where `n` is
    /// the number of bytes it was able to read starting at `address`. **Note
    /// that this value may be smaller than you requested, or zero.** This
    /// indicates that fewer than `dest.len()` contiguous bytes _exist_ starting
    /// at `address`. This may be due to: address space holes, incomplete dumps,
    /// reading an ELF file without a RAM image, etc.
    ///
    /// These holes are a valid part of the machine state, and so this is not
    /// failure.
    ///
    /// Failure happens if we can't _access_ the machine state to find this out,
    /// or to get the data -- for instance, if a USB transaction to a JTAG probe
    /// fails, or if we get a filesystem error reading an ELF file. In that
    /// case, we'll return `Err`.
    fn read_memory(&self, address: u64, dest: &mut [u8]) -> Result<usize, Self::Error>;
}

#[derive(Clone)]
pub struct ImgMachine {
    img: Vec<u8>,
}

impl ImgMachine {
    pub fn new(img: impl Into<Vec<u8>>) -> Self {
        Self {
            img: img.into(),
        }
    }
}

impl Machine for ImgMachine {
    type Error = Infallible;

    fn read_memory(&self, address: u64, dest: &mut [u8]) -> Result<usize, Self::Error> {
        let Ok(address) = usize::try_from(address) else { return Ok(0) };
        let end = address.checked_add(dest.len())
            .unwrap_or(usize::MAX);
        let end = usize::min(end, self.img.len());
        let Some(chunk) = end.checked_sub(address) else { return Ok(0) };

        dest[..chunk].copy_from_slice(&self.img[address..end]);
        Ok(chunk)
    }
}

impl Machine for RangeInclusiveMap<u64, Vec<u8>> {
    type Error = Infallible;

    fn read_memory(&self, address: u64, dest: &mut [u8]) -> Result<usize, Self::Error> {
        let Some((range, segment)) = self.get_key_value(&address) else { return Ok(0) };
        let offset = address - range.start();

        let Ok(offset) = usize::try_from(offset) else { return Ok(0) };
        let end = offset.checked_add(dest.len())
            .unwrap_or(usize::MAX);
        let end = usize::min(end, segment.len());
        let Some(chunk) = end.checked_sub(offset) else { return Ok(0) };

        dest[..chunk].copy_from_slice(&segment[offset..end]);
        Ok(chunk)
    }
}

#[derive(Clone, Debug, Error)]
pub enum LoadError<E> {
    #[error("tuple type missing member {0}")]
    MissingTupleMember(usize),
    #[error("struct was not tuple-like")]
    NotATuple,
    #[error("not a struct")]
    NotAStruct,
    #[error("expected encoding {expected:?}, type had encoding {got:?}")]
    WrongEncoding { expected: Encoding, got: Encoding },
    #[error("expected type with size {expected}, but type had size {got}")]
    WrongSize { expected: u64, got: u64 },
    #[error("base type required")]
    NotABase,
    #[error("enum type required")]
    NotAnEnum,
    #[error("C-like enum type required")]
    NotACEnum,
    #[error("pointer type required")]
    NotAPointer,
    #[error("array type is not finite and can't be loaded")]
    InfiniteArray,
    #[error("arrays with non-zero lower bounds ({0}) are not supported")]
    NonZeroLowerBound(u64),
    #[error("array has element type without defined size")]
    UnsizedElement,
    #[error("array too big: {count} x {elt_size}-byte elements")]
    ArrayTooBig {
        count: u64,
        elt_size: u64,
    },
    #[error("type too big for this platform: {0} bytes")]
    TypeTooBig(u64),
    #[error("array type required")]
    NotAnArray,
    #[error("expected enum with {expected} variants, found {got}")]
    WrongVariantCount { expected: usize, got: usize },
    #[error("unexpected variant: {0}")]
    UnexpectedVariant(String),
    #[error("expected struct/tuple with {expected} members, found {got}")]
    WrongMemberCount { expected: usize, got: usize },
    #[error("can't load an uninhabited (empty) enum")]
    Uninhabited,
    #[error("discriminator value {0} not valid for type")]
    BadDiscriminator(u64),
    #[error("unsupported type (TODO)")]
    UnsupportedType,
    #[error("expected member `{0}` not found")]
    MissingMember(String),
    #[error("a type named {expected} was required, but found: {got}")]
    WrongTypeName { expected: String, got: String},
    #[error("some of the bytes required to load this type are not present in the machine")]
    DataUnavailable,

    #[error("an error occurred accessing the underlying machine state")]
    Machine(#[from] E),
}

/*

impl<A: Load, B: Load> Load for (A, B) {
    fn from_state<M: Machine>(
        machine: &M,
        addr: u64,
        world: &DebugDb,
        ty: &Type,
    ) -> Result<Self, LoadError<M::Error>> {
        if let Type::Struct(s) = ty {
            if s.tuple_like {
                let m0 = s.unique_member("__0")
                    .ok_or(LoadError::MissingTupleMember(0))?;
                let m0ty = world.type_by_id(m0.type_id).unwrap();
                let m1 = s.unique_member("__1")
                    .ok_or(LoadError::MissingTupleMember(0))?;
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
                Err(LoadError::NotATuple)
            }
        } else {
            Err(LoadError::NotAStruct)
        }
    }
}
*/

fn generic_base_load<M: Machine, B, const N: usize>(
    encoding: Encoding,
    ty: &Type,
    machine: &M,
    addr: u64,
    extract: impl FnOnce([u8; N]) -> B,
) -> Result<B, LoadError<M::Error>> {
    if let Type::Base(b) = ty {
        if b.encoding != encoding {
            return Err(LoadError::WrongEncoding {
                expected: encoding,
                got: b.encoding,
            });
        }
        if b.byte_size != N as u64 {
            return Err(LoadError::WrongSize {
                expected: N as u64,
                got: b.byte_size,
            });
        }
        let mut ary = [0; N];
        let n = machine.read_memory(addr, &mut ary)?;
        if n != N {
            return Err(LoadError::DataUnavailable);
        }
        Ok(extract(ary))
    } else {
        Err(LoadError::NotABase)
    }
}

impl Load for u8 {
    fn from_state<M: Machine>(
        machine: &M,
        addr: u64,
        _world: &DebugDb,
        ty: &Type,
    ) -> Result<u8, LoadError<M::Error>> {
        generic_base_load(
            Encoding::Unsigned,
            ty,
            machine,
            addr,
            |[b]| b,
        )
    }
}

impl Load for i8 {
    fn from_state<M: Machine>(
        machine: &M,
        addr: u64,
        _world: &DebugDb,
        ty: &Type,
    ) -> Result<Self, LoadError<M::Error>> {
        generic_base_load(
            Encoding::Signed,
            ty,
            machine,
            addr,
            |[b]| b as i8,
        )
    }
}

macro_rules! base_impl {
    ($t:ty, $sz:expr, $enc:ident, $read:ident) => {
        impl Load for $t {
            fn from_state<M: Machine>(
                machine: &M,
                addr: u64,
                world: &DebugDb,
                ty: &Type,
            ) -> Result<Self, LoadError<M::Error>> {
                generic_base_load::<_, $t, $sz>(
                    Encoding::$enc,
                    ty,
                    machine,
                    addr,
                    |a| world.endian().$read(&a),
                )
            }
        }
    };
}

base_impl!(u16, 2, Unsigned, read_u16);
base_impl!(u32, 4, Unsigned, read_u32);
base_impl!(u64, 8, Unsigned, read_u64);

base_impl!(i16, 2, Signed, read_i16);
base_impl!(i32, 4, Signed, read_i32);
base_impl!(i64, 8, Signed, read_i64);

impl Load for core::sync::atomic::AtomicU32 {
    fn from_state<M: Machine>(
        machine: &M,
        addr: u64,
        world: &DebugDb,
        ty: &Type,
    ) -> Result<Self, LoadError<M::Error>> {
        let Type::Struct(ty) = ty else {
            return Err(LoadError::NotAStruct);
        };
        if ty.name != "core::sync::atomic::AtomicU32" {
            return Err(LoadError::WrongTypeName {
                expected: "core::sync::atomic::AtomicU32".to_string(),
                got: ty.name.clone(),
            });
        }
        let Some(m_v) = ty.unique_member("v") else {
            return Err(LoadError::MissingMember("v".to_string()));
        };
        let unsafecell = world.type_by_id(m_v.type_id).unwrap();
        let Type::Struct(unsafecell) = unsafecell else {
            return Err(LoadError::NotAStruct);
        };
        if unsafecell.name != "core::cell::UnsafeCell<u32>" {
            return Err(LoadError::WrongTypeName {
                expected: "core::cell::UnsafeCell<u32>".to_string(),
                got: unsafecell.name.clone(),
            });
        }
        let Some(m_value) = unsafecell.unique_member("value") else {
            return Err(LoadError::MissingMember("value".to_string()));
        };

        let value_ty = world.type_by_id(m_value.type_id).unwrap();
        
        let x = u32::from_state(machine, addr, world, value_ty)?;
        Ok(core::sync::atomic::AtomicU32::new(x))
    }
}

impl<T: Load> Load for Vec<T> {
    fn from_state<M: Machine>(
        machine: &M,
        addr: u64,
        world: &DebugDb,
        ty: &Type,
    ) -> Result<Self, LoadError<M::Error>> {
        if let Type::Array(s) = ty {
            let count = s.count.ok_or(LoadError::InfiniteArray)?;
            if s.lower_bound != 0 {
                return Err(LoadError::NonZeroLowerBound(s.lower_bound));
            }
            let elty = world.type_by_id(s.element_type_id).unwrap();

            let elt_size = elty
                .byte_size(world)
                .ok_or(LoadError::UnsizedElement)?;
            let elt_size = elt_size.max(elty.alignment(world).unwrap_or(0));

            let mut elts = Vec::with_capacity(usize::try_from(count).unwrap());
            for i in 0..count {
                elts.push(T::from_state(machine, addr + i * elt_size, world, elty)?);
            }
            Ok(elts)
        } else {
            Err(LoadError::NotAnArray)
        }
    }
}

/*

/// A `Load` impl for Option-shaped types.
///
/// This will work for any enum with two variants, where one is named None and
/// has no payload, and the other is named Some and has one field.
impl<T: Load> Load for Option<T> {
    fn from_state<M: Machine>(
        machine: &M,
        addr: u64,
        world: &DebugDb,
        ty: &Type,
    ) -> Result<Self, LoadError<M::Error>> {
        let Type::Enum(s) = ty else {
            return Err(LoadError::NotAnEnum);
        };
        // Option-like enums have two variants.
        if let VariantShape::Many { variants, .. } = &s.shape {
            if variants.len() != 2 {
                return Err(LoadError::WrongVariantCount {
                    expected: 2,
                    got: variants.len(),
                });
            }
            // Those variants are named None and Some.
            for v in variants.values() {
                if let Some(n) = &v.member.name {
                    if n == "None" || n == "Some" {
                        continue;
                    }
                    return Err(LoadError::UnexpectedVariant(n.clone()));
                }
            }
        }
        // Ok, that's the extent of the type validation I'm comfortable
        // doing here for performance reasons.

        let v = choose_variant(buffer, addr, world, s)?;
        let is_some = v.member.name.as_ref().unwrap() == "Some";
        let vty = world.type_by_id(v.member.type_id).unwrap();
        // Option-like enums have tuple variants.
        let Type::Struct(s) = vty else {
            // TODO: this error is probably not descriptive enough.
            return Err(LoadError::NotAStruct);
        };
        if !s.tuple_like {
            // TODO: this error is probably not descriptive enough.
            return Err(LoadError::NotATuple);
        }
        if is_some {
            if s.members.len() != 1 {
                return Err(LoadError::WrongMemberCount {
                    expected: 1,
                    got: s.members.len(),
                });
            }

            let m = &s.members[0];
            let mty =
                world.type_by_id(m.type_id).unwrap();
            let ma = addr + usize::try_from(m.location).unwrap();
            Ok(Some(T::from_buffer(buffer, ma, world, mty)?))
        } else {
            if !s.members.is_empty() {
                return Err(LoadError::WrongMemberCount {
                    expected: 0,
                    got: s.members.len(),
                });
            }
            Ok(None)
        }
    }
}
*/

pub(crate) fn choose_variant<'e, M: Machine>(
    machine: &M,
    addr: u64,
    world: &'e DebugDb,
    e: &'e Enum,
) -> Result<&'e Variant, LoadError<M::Error>> {
    match &e.shape {
        VariantShape::Zero => {
            Err(LoadError::Uninhabited)
        }
        VariantShape::One(v) => Ok(v),
        VariantShape::Many {
            member, variants, ..
        } => {
            let dtype_id = member.type_id;
            let dty = world.type_by_id(dtype_id).unwrap();
            let da = addr + member.location;
            let dsize = usize::try_from(dty.byte_size(world).unwrap()).unwrap();
            let d = load_unsigned(world.endian(), machine, da, dsize)?
                .ok_or(LoadError::DataUnavailable)?;
            let v = variants
                .get(&Some(d))
                .or_else(|| variants.get(&None))
                .ok_or(LoadError::BadDiscriminator(d))?;
            Ok(v)
        }
    }
}

pub(crate) fn load_unsigned<M: Machine>(
    endian: gimli::RunTimeEndian,
    machine: &M,
    addr: u64,
    size: usize,
) -> Result<Option<u64>, M::Error> {
    let mut buffer = [0; 8];
    let buffer = &mut buffer[..size];
    let n = machine.read_memory(addr, buffer)?;
    Ok(if n < size {
        None
    } else {
        Some(match size {
            1 => u64::from(buffer[0]),
            2 => u64::from(endian.read_u16(buffer)),
            4 => u64::from(endian.read_u32(buffer)),
            8 => endian.read_u64(buffer),
            _ => unimplemented!(),
        })
    })
}
/*
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
*/
