//! Data model types.
//!
//! This is our abstract description of types and routines in a program.

use std::borrow::Cow;
use std::hash::Hash;
use std::num::NonZeroU64;
use crate::DebugDb;
use indexmap::IndexMap;

/// Identifies a specific type within a program, using its offset within the
/// debug section(s).
///
/// Sometimes types appear more than once in debug info. In that case, each type
/// will have a distinct `TypeId`.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct TypeId(pub gimli::UnitSectionOffset);

impl From<gimli::UnitSectionOffset> for TypeId {
    fn from(x: gimli::UnitSectionOffset) -> Self {
        Self(x)
    }
}

/// Identifies a subprogram within a program -- a function or subroutine.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ProgramId(pub gimli::UnitSectionOffset);

impl From<gimli::UnitSectionOffset> for ProgramId {
    fn from(x: gimli::UnitSectionOffset) -> Self {
        Self(x)
    }
}

/// Identifies a static variable.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct VarId(pub gimli::UnitSectionOffset);

impl From<gimli::UnitSectionOffset> for VarId {
    fn from(x: gimli::UnitSectionOffset) -> Self {
        Self(x)
    }
}

/// Information about a type from a program.
///
/// There are many kinds of types; this enum distinguishes between them.
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
    Unresolved(Unresolved),
}

impl Type {
    /// Returns the location of the type's definition within the debug info
    /// section(s).
    pub fn offset(&self) -> gimli::UnitSectionOffset {
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
            Self::Unresolved(s) => s.offset,
        }
    }

    /// Determines the alignment of the type, in bytes.
    ///
    /// Not all types have alignment.
    pub fn alignment(&self, world: &DebugDb) -> Option<u64> {
        match self {
            Self::Struct(s) => s.alignment,
            Self::Enum(s) => s.alignment,
            Self::Base(s) => s.alignment,
            Self::CEnum(s) => s.alignment,
            Self::Union(s) => Some(s.alignment),
            Self::Array(a) => {
                let eltty = world.type_by_id(a.element_type_id)?;
                eltty.alignment(world)
            }
            Self::Pointer(_) => Some(world.pointer_size() as u64),

            _ => None,
        }
    }

    /// Determines the inherent size of the type, in bytes. The inherent size is
    /// the size that can be computed without referring to the debug information
    /// of other types.
    ///
    /// Not all types have sizes; even fewer have inherent sizes. This is an
    /// implementation detail of the full `byte_size` algorithm.
    pub fn inherent_byte_size(&self) -> Option<u64> {
        match self {
            Self::Struct(s) => s.byte_size,
            Self::Enum(s) => s.byte_size,
            Self::Base(s) => Some(s.byte_size),
            Self::CEnum(s) => Some(s.byte_size),
            Self::Union(s) => Some(s.byte_size),

            _ => None,
        }
    }

    pub(crate) fn byte_size_early<'a>(
        &'a self,
        pointer_size: usize,
        lookup_type: impl Fn(TypeId) -> Option<&'a Type>,
    ) -> Option<u64> {
        let mut factor = 1;
        let mut t = self;
        loop {
            match t.inherent_byte_size() {
                Some(x) => break Some(factor * x),
                None => match t {
                    Self::Array(a) => {
                        factor *= a.count?;
                        t = lookup_type(a.element_type_id)?;
                    }
                    Self::Pointer(_) => break Some(factor * pointer_size as u64),
                    Self::Subroutine(_) => break None,

                    _ => panic!("inconsistency btw byte_size_early and inherent_byte_size"),
                },
            }
        }
    }

    /// Determines the size of the type, in bytes.
    ///
    /// Not all types have sizes.
    pub fn byte_size(&self, world: &DebugDb) -> Option<u64> {
        self.byte_size_early(
            world.pointer_size(),
            |t| world.type_by_id(t),
        )
    }

    /// Determines the name of the type.
    pub fn name(&self, world: &DebugDb) -> Cow<'_, str> {
        match self {
            Self::Struct(s) => (&s.name).into(),
            Self::Enum(s) => (&s.name).into(),
            Self::Base(s) => (&s.name).into(),
            Self::CEnum(s) => (&s.name).into(),
            Self::Union(s) => (&s.name).into(),
            Self::Pointer(s) => {
                if let Some(assigned_name) = &s.name {
                    assigned_name.into()
                } else {
                    let pointee_name = world
                        .type_by_id(s.type_id)
                        .map(|t| t.name(world))
                        .unwrap_or("???".into());
                    format!("*_ {pointee_name}").into()
                }
            }
            Self::Array(a) => {
                let eltname = world
                    .type_by_id(a.element_type_id)
                    .map(|t| t.name(world))
                    .unwrap_or("???".into());

                if let Some(n) = a.count {
                    format!("[{}; {}]", eltname, n).into()
                } else {
                    format!("[{}; ???]", eltname).into()
                }
            }
            Self::Subroutine(_) => "subroutine".into(), // TODO
            Self::Unresolved(_) => "<UNRESOLVED>".into(),
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

/// A "base type," also known as a "primitive type," is not constructed by
/// aggregating other types. Examples in Rust include `u32` and `bool`.
///
/// Note that, in Rust in particular, there are several "base types" that you
/// might not think of as such. Both `()` and `!` are represented as zero-sized
/// base types.
#[derive(Clone, Debug)]
pub struct Base {
    /// Name of the type.
    pub name: String,
    /// How to interpret the type's bits.
    pub encoding: Encoding,
    /// Number of bytes in a value of the type.
    pub byte_size: u64,
    /// Explicit alignment, if given.
    pub alignment: Option<u64>,
    /// Location in debug info.
    pub offset: gimli::UnitSectionOffset,
}

/// A "struct type" describes a record containing members, each of which has its
/// own type.
///
/// Rust defines both normal structs (with named members) and _tuple structs_
/// (with numbered members). This type is used for both. A tuple struct will
/// have the `tuple_like` flag set, and its members will be in numeric order.
/// (They can also be accessed by names of the form `__0`, `__1`, etc.)
#[derive(Debug, Clone)]
pub struct Struct {
    /// Name of the struct type.
    pub name: String,
    /// Size of a value of this struct in bytes.
    pub byte_size: Option<u64>,
    /// Alignment required for values of this struct.
    pub alignment: Option<u64>,
    /// If this struct is generic, a list of template parameters. Non-generic
    /// structs have an empty list.
    pub template_type_parameters: Vec<TemplateTypeParameter>,
    /// When `true`, this struct appears to originate from a Rust "tuple struct"
    /// with numbered fields. When `false`, this is a normal struct.
    pub tuple_like: bool,
    /// Member fields of the struct.
    ///
    /// These are in an `IndexMap` so that order is preserved. The members are
    /// recorded in the order they appear in the debug info, which in practice
    /// is also the order they're declared in the source. They are _not_ in
    /// order of position in the struct in memory.
    pub members: Vec<Member>,
    /// Location in debug info.
    pub offset: gimli::UnitSectionOffset,
    /// Location of the declaration of this subprogram in the source.
    pub decl_coord: DeclCoord,
}

impl Struct {
    pub fn unique_member(&self, name: &str) -> Option<&Member> {
        let mut matches = self.members.iter()
            .filter(|m| m.name.as_deref() == Some(name));
        let first = matches.next()?;
        if matches.next().is_some() {
            // There is no _unique_ member by this name.
            None
        } else {
            Some(first)
        }
    }
}

/// An "enum type," in the Rust sense of the term, is a tagged union (or
/// discriminated union). It can contain multiple different types of values, but
/// only one at a time, and the options are distinguished through a
/// "discriminator" member -- except if there is only one variant, in which case
/// the compiler usually eliminates that member. See `VariantShape` for details.
///
/// This library distinguishes between Rust-style enums (this type) and C-style
/// enums (the `CEnum`) type. Rust programs will generate C-style enums when
/// none of the enum variants have a payload or fields.
#[derive(Debug, Clone)]
pub struct Enum {
    /// Name of the enum type.
    pub name: String,
    /// Size of a value of the enum type, in bytes.
    pub byte_size: Option<u64>,
    /// Alignment required for values of this enum.
    pub alignment: Option<u64>,
    /// If this struct is generic, a list of template parameters. Non-generic
    /// structs have an empty list.
    pub template_type_parameters: Vec<TemplateTypeParameter>,
    /// Description of the variants in this enum.
    pub shape: VariantShape,
    /// Location in debug info.
    pub offset: gimli::UnitSectionOffset,
}

/// A "C-style enum" type -- a type with several value variants, each of which
/// can be represented by an integer.
#[derive(Debug, Clone)]
pub struct CEnum {
    /// Name of the enum type.
    pub name: String,
    /// Representation type.
    pub repr_type_id: TypeId,
    /// Flag indicating that this enum is a distinct type, rather than
    /// evaluating as values of some base type. This is set for all enums in
    /// Rust, some enums in C++, and no enums in C.
    pub enum_class: bool,
    /// Size of a value of the enum type, in bytes.
    pub byte_size: u64,
    /// Alignment required for values of this enum.
    pub alignment: Option<u64>,
    /// Variants ("enumerators") of this type.
    pub enumerators: IndexMap<u64, Enumerator>,
    /// Location in debug info.
    pub offset: gimli::UnitSectionOffset,
}

/// An array type.
///
/// An array consists of an element type and a count. Not all array types in
/// DWARF have counts, but in Rust, they do.
///
/// Array types can also technically have a `lower_bound` that is not 0, but in
/// practice to observe this you need to link with a Modula or Fortran binary.
#[derive(Debug, Clone)]
pub struct Array {
    /// Type of elements of the array.
    pub element_type_id: TypeId,
    /// Type of the array index. This is synthetic and rarely useful; all Rust
    /// arrays point to the same index type.
    pub index_type_id: TypeId,
    /// First index in the array. Always 0 in Rust and C.
    pub lower_bound: u64,
    /// Number of elements in the array, if specified.
    pub count: Option<u64>,
    /// Location in debug info.
    pub offset: gimli::UnitSectionOffset,
}

/// A pointer type.
///
/// There are many flavors of pointers -- `const`, not-`const`, Rust references,
/// C raw pointers, etc. This models them all. The differences between them are
/// not present in DWARF -- though they can be inferred from the `name`.
///
/// Pointer size is implicit and fixed for the whole program; it can be queried
/// from the `DebugDb` instance.
#[derive(Debug, Clone)]
pub struct Pointer {
    /// Type of data this points _to_.
    pub type_id: TypeId,
    /// Name of the pointer type. Compilers don't name all pointer types.
    pub name: Option<String>,
    /// Location in debug info.
    pub offset: gimli::UnitSectionOffset,
}

/// A C-style non-tagged union.
///
/// A union has multiple members, like a struct, except that those members are
/// overlaid in memory, and only one is valid at a time. Unlike an `Enum`, there
/// is no information in union to tell you _which_ variant is valid.
#[derive(Debug, Clone)]
pub struct Union {
    /// Name of this union type.
    pub name: String,
    /// Size of a value of this union type, in bytes.
    pub byte_size: u64,
    /// Alignment required for a value of this union type, in bytes.
    pub alignment: u64,
    /// If this union is generic, this contains an array of template type
    /// parameters. If it is not generic, this is empty.
    pub template_type_parameters: Vec<TemplateTypeParameter>,
    /// Members of the union in declaration order.
    pub members: Vec<Member>,
    /// Location in debug info.
    pub offset: gimli::UnitSectionOffset,
}

/// A subroutine type. Note that this is different from a `Subprogram` -- this
/// is used as the pointed-to type for function pointers.
#[derive(Clone, Debug)]
pub struct Subroutine {
    /// Type of value returned, if any. In both C and Rust, functions that
    /// return nothing (`void` and `()`, respectively) have no return type,
    /// rather than `Some(typeid_of_void)`.
    pub return_type_id: Option<TypeId>,
    /// Types of parameters to a routine of this type.
    pub formal_parameters: Vec<TypeId>,
    /// Location in debug info.
    pub offset: gimli::UnitSectionOffset,
}

/// A type that was not found in the debug info.
///
/// Usually this is because it's not actually used in the program, and only
/// indirectly referenced.
#[derive(Debug, Clone)]
pub struct Unresolved {
    /// Location in debug info.
    pub offset: gimli::UnitSectionOffset,
}

/// Possible encodings for a `Base` type.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Encoding {
    /// Unsigned integer.
    Unsigned,
    /// Signed integer.
    Signed,
    /// Unsigned char. This is used for Rust `char` (with `byte_size == 4`) as
    /// well as for C `unsigned char` (`byte_size == 1`) and sometimes for C
    /// `char` depending on the platform ABI because reasons.
    UnsignedChar,
    /// Unsigned char. This is used for C `unsigned char` (`byte_size == 1`) and
    /// sometimes for C `char` depending on the platform ABI because reasons.
    SignedChar,
    /// Boolean -- 0 is false, non-zero is true.
    ///
    /// In Rust, true is always 1, but DWARF doesn't seem to mandate that, and
    /// so here we are.
    Boolean,
    /// IEEE754 floating point number.
    Float,
    /// IEEE754 complex floating point number, i.e. probably a pair of floats.
    /// Support for this encoding is currently somewhat limited as none of our
    /// programs use complex floats.
    ///
    /// Note that this encoding is specific to the `__Complex` C language
    /// extension, and is _not used_ for Rust complex numbers.
    ComplexFloat,

    UtfChar,
}

/// Information on a type parameter binding for an instance of a generic type.
///
/// This is called "Template Type Parameter" because that's what DWARF calls it,
/// because DWARF is rather C-specific.
#[derive(Debug, Clone)]
pub struct TemplateTypeParameter {
    /// Name of parameter.
    pub name: String,
    /// Type the parameter is bound to.
    pub type_id: TypeId,
}

/// A component of a struct or union.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Member {
    /// Name of the member. Not all members have names, though in Rust they all
    /// do.
    pub name: Option<String>,
    /// If `true`, this member is compiler-generated and will not make very much
    /// sense to the user.
    pub artificial: bool,
    /// Type of data stored in this member.
    pub type_id: TypeId,
    /// Alignment specified for this member. If missing, check the alignment for
    /// `type_id`.
    pub alignment: Option<u64>,
    /// Offset of this member within the enclosing type.
    pub location: u64,
    /// Location in debug info.
    pub offset: gimli::UnitSectionOffset,
    pub decl_coord: DeclCoord,
}

/// Description of the potential variant shapes for a Rust-style enum (tagged
/// union).
#[derive(Debug, Clone)]
pub enum VariantShape {
    /// The enum has no variants. No discriminator member has been generated.
    /// These enums are typically zero-sized.
    Zero,
    /// The enum contains only one variant, and so the compiler has not
    /// generated a discriminator member, because it would go unused. The
    /// `Variant` is embedded directly.
    One(Variant),
    /// The enum contains a discriminator. This generally implies that there are
    /// two or more variants, though nothing in the spec requires this.
    Many {
        /// Location of the definition of the discriminator in debug info.
        discr: gimli::UnitSectionOffset,
        /// Member describing the discriminator. Note that this member will
        /// typically be nameless.
        member: Member,
        /// Variants that may be selected depending on the value of the
        /// discriminator. The key `None` is used for a "default" `Variant` that
        /// is chosen if none of the explicit values match; this is used to
        /// implement various enum layout optimizations in Rust.
        variants: IndexMap<Option<u64>, Variant>,
    },
}

/// A variant of a Rust-style enum.
#[derive(Debug, Clone)]
pub struct Variant {
    /// Member containing the variant's data. An enum in Rust that is not
    /// C-style always has data in every variant, but if the variant has no
    /// fields from the user's perspective, the embedded data will be an empty
    /// struct.
    pub member: Member,
    /// Location in debug info.
    pub offset: gimli::UnitSectionOffset,
    pub decl_coord: DeclCoord,
}

/// One of the options in a C-style enum type.
#[derive(Debug, Clone)]
pub struct Enumerator {
    /// Name of this variant.
    pub name: String,
    /// Numeric value associated with this invariant.
    pub const_value: u64,
    /// Location in debug info.
    pub offset: gimli::UnitSectionOffset,
}

/// A function or subroutine in a program.
///
/// Note that this is different from `Subroutine`, which defines the _type_ of a
/// function; this defines the _identity_ of a function.
#[derive(Clone, Debug)]
pub struct Subprogram {
    /// Name of the subprogram. Not all subprograms have names. TODO: why not?
    pub name: Option<String>,
    /// Range of PC values that are contained within the code generated for this
    /// subprogram, when code has been generated at the top level (i.e. the
    /// subprogram is not inlined).
    ///
    /// Subprograms that are completely inlined will often have nonsense
    /// `pc_range` values starting at address 0.
    pub pc_range: Option<std::ops::Range<u64>>,
    /// Location of the declaration of this subprogram in the source.
    pub decl_coord: DeclCoord,
    /// If this subprogram is an instance of a generic subprogram, this provides
    /// the bindings for the type parameters. If this subprogram is not generic,
    /// this is empty.
    pub template_type_parameters: Vec<TemplateTypeParameter>,
    /// Type returned by subprogram, or `None` for `()`/`void`.
    pub return_type_id: Option<TypeId>,
    /// Information about parameters needed by this subprogram.
    pub formal_parameters: Vec<SubParameter>,
    /// Subprograms that have been inlined into this one.
    pub inlines: Vec<InlinedSubroutine>,
    /// If this subprogram represents a specialization of another, this provides
    /// a link to the prototype. The prototype may have information that this
    /// record does not, such as a valid name.
    pub abstract_origin: Option<gimli::UnitSectionOffset>,
    /// Actual symbol name used to refer to this subprogram, if it is different
    /// from `name` -- which it tends to be in languages with hierarchical
    /// namespaces.
    pub linkage_name: Option<String>,
    /// If `true`, this subprogram is expected not to return, meaning that any
    /// code after a call to this subprogram is theoretically unreachable.
    ///
    /// In Rust, `noreturn` functions tend to have `!` as their return type.
    pub noreturn: bool,
    /// Location in debug info.
    pub offset: gimli::UnitSectionOffset,
}

/// Parameter to a subprogram.
///
/// This is more detailed than the `formal_parameters` used for function type
/// definitions.
///
/// Note that it's common for subprogram parameters to be abstract. In that
/// case, most useful content will be missing from `SubParameter`, and you'll
/// need to go consult the `abstract_origin`.
#[derive(Clone, Debug)]
pub struct SubParameter {
    /// Name of parameter, if available.
    pub name: Option<String>,
    /// Location of declaration of this parameter in the source.
    pub decl_coord: DeclCoord,
    /// Type of the parameter, if available.
    pub type_id: Option<TypeId>,
    /// Reference to a different `SubParameter` that this specializes.
    pub abstract_origin: Option<gimli::UnitSectionOffset>,
    /// Fixed value for this parameter. This can happen in cases where a
    /// specialized `Subprogram` fixes one or more parameter values to
    /// constants.
    ///
    /// TODO: type probably needs to be more general.
    pub const_value: Option<u64>,
    /// Location in debug info.
    pub offset: gimli::UnitSectionOffset,
}

/// File "coordinates" -- path, line number, column number.
///
/// Note that, in accordance with tradition, both lines and columns are numbered
/// starting at one.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct DeclCoord {
    /// Path to source file, if available.
    pub file: Option<String>,
    /// Line number, if available.
    pub line: Option<NonZeroU64>,
    /// Column number, if available.
    pub column: Option<NonZeroU64>,
}

impl DeclCoord {
    pub fn is_useful(&self) -> bool {
        self.file.is_some() || self.line.is_some() || self.column.is_some()
    }
}

/// Information about a subroutine that has been inlined into a subprogram.
#[derive(Clone, Debug)]
pub struct InlinedSubroutine {
    /// Location of the subprogram abstract root that defines this.
    pub abstract_origin: Option<gimli::UnitSectionOffset>,
    /// Ranges of PC values that are included in this inlined subroutine.
    pub pc_ranges: Vec<gimli::Range>,
    /// Location of the callsite that was inlined.
    pub call_coord: DeclCoord,
    /// Further inlined subroutines within this one.
    pub inlines: Vec<InlinedSubroutine>,
    /// Definition of the formal parameters to this inlined subroutine.
    pub formal_parameters: Vec<SubParameter>,
    /// Location in debug info.
    pub offset: gimli::UnitSectionOffset,
}

/// A row of the computed line number table.
#[derive(Clone, Debug)]
pub struct LineNumberRow {
    /// Range of PC values that should use this entry.
    pub pc_range: std::ops::Range<u64>,
    /// Filename.
    pub file: String,
    /// Line number, if available.
    pub line: Option<NonZeroU64>,
    /// Column number, if available.
    pub column: Option<NonZeroU64>,
}

/// Information about a static stack frame associated with a PC value.
///
/// TODO: the name of this type should become more meaningful as we learn how it
/// is used.
pub struct PcInfo {
    /// Subprogram being run.
    pub subprogram: ProgramId,
    /// File containing code being run.
    pub file: String,
    /// Line number of code being run, if available.
    pub line: Option<NonZeroU64>,
    /// Column number of code being run, if available.
    pub column: Option<NonZeroU64>,
}

/// A static variable with a fixed address.
#[derive(Clone, Debug)]
pub struct StaticVariable {
    /// Name of variable.
    pub name: String,
    /// Type contained in variable.
    pub type_id: TypeId,
    /// Location of variable declaration.
    pub decl: DeclCoord,
    /// Address in memory.
    pub location: u64,
    /// Location in debug info.
    pub offset: gimli::UnitSectionOffset,
}

pub trait Equiv {
    /// Tests if `self` and `other` are structurally equivalent, such that they
    /// could be unified into a single definition despite appearing in separate
    /// compilation units.
    ///
    /// Returns `None` if there is no way to make the definitions match, or
    /// `Some(tids)` if the definitions match if all the types in `tids` are
    /// also equivalent to each other.
    fn equiv(&self, other: &Self) -> Option<Vec<(TypeId, TypeId)>>;
}

impl Equiv for TypeId {
    fn equiv(&self, other: &Self) -> Option<Vec<(TypeId, TypeId)>> {
        Some(vec![(*self, *other)])
    }
}

impl Equiv for Member {
    fn equiv(&self, other: &Self) -> Option<Vec<(TypeId, TypeId)>> {
        let self_easy = (&self.name, self.artificial, self.alignment, self.location);
        let other_easy = (&other.name, other.artificial, other.alignment, other.location);
        if self_easy != other_easy {
            return None;
        }

        Some(vec![(self.type_id, other.type_id)])
    }
}

impl Equiv for Variant {
    fn equiv(&self, other: &Self) -> Option<Vec<(TypeId, TypeId)>> {
        self.member.equiv(&other.member)
    }
}

impl Equiv for VariantShape {
    fn equiv(&self, other: &Self) -> Option<Vec<(TypeId, TypeId)>> {
        match (self, other) {
            (Self::Zero, Self::Zero) => Some(vec![]),
            (Self::One(a), Self::One(b)) => a.equiv(b),
            (Self::Many { member: ma, variants: va, .. }, Self::Many { member: mb, variants: vb, .. }) => {
                let mut conditions = vec![];
                conditions.extend(ma.equiv(mb)?);
                conditions.extend(va.equiv(vb)?);
                Some(conditions)
            }
            _ => None,
        }
    }
}

impl Equiv for TemplateTypeParameter {
    fn equiv(&self, other: &Self) -> Option<Vec<(TypeId, TypeId)>> {
        if self.name != other.name {
            return None;
        }

        Some(vec![(self.type_id, other.type_id)])
    }
}

impl<T> Equiv for Vec<T>
    where T: Equiv,
{
    fn equiv(&self, other: &Self) -> Option<Vec<(TypeId, TypeId)>> {
        if self.len() != other.len() {
            return None;
        }

        let mut conditions = vec![];
        for (a, b) in self.iter().zip(other) {
            conditions.extend(a.equiv(b)?);
        }
        Some(conditions)
    }
}

impl<T> Equiv for Option<T>
    where T: Equiv,
{
    fn equiv(&self, other: &Self) -> Option<Vec<(TypeId, TypeId)>> {
        match (self, other) {
            (Some(a), Some(b)) => a.equiv(b),
            _ => None
        }
    }
}

impl<K, T> Equiv for IndexMap<K, T>
    where T: Equiv,
          K: Eq + Hash,
{
    fn equiv(&self, other: &Self) -> Option<Vec<(TypeId, TypeId)>> {
        if self.len() != other.len() {
            return None;
        }

        let mut conditions = vec![];
        for (ak, a) in self {
            conditions.extend(a.equiv(other.get(ak)?)?);
        }
        Some(conditions)
    }
}

impl Equiv for Struct {
    fn equiv(&self, other: &Self) -> Option<Vec<(TypeId, TypeId)>> {
        let self_easy = (&self.name, self.byte_size, self.alignment, self.tuple_like);
        let other_easy = (&other.name, other.byte_size, other.alignment, other.tuple_like);
        if self_easy != other_easy {
            return None;
        }

        let mut conditions = vec![];
        conditions.extend(self.template_type_parameters.equiv(&other.template_type_parameters)?);
        conditions.extend(self.members.equiv(&other.members)?);

        Some(conditions)
    }
}

impl Equiv for Union {
    fn equiv(&self, other: &Self) -> Option<Vec<(TypeId, TypeId)>> {
        let self_easy = (&self.name, self.byte_size, self.alignment);
        let other_easy = (&other.name, other.byte_size, other.alignment);
        if self_easy != other_easy {
            return None;
        }

        let mut conditions = vec![];
        conditions.extend(self.template_type_parameters.equiv(&other.template_type_parameters)?);
        conditions.extend(self.members.equiv(&other.members)?);

        Some(conditions)
    }
}

impl Equiv for Enum {
    fn equiv(&self, other: &Self) -> Option<Vec<(TypeId, TypeId)>> {
        let self_easy = (&self.name, self.byte_size, self.alignment);
        let other_easy = (&other.name, other.byte_size, other.alignment);
        if self_easy != other_easy {
            return None;
        }

        let mut conditions = vec![];
        conditions.extend(self.template_type_parameters.equiv(&other.template_type_parameters)?);
        conditions.extend(self.shape.equiv(&other.shape)?);

        Some(conditions)
    }
}

impl Equiv for Pointer {
    fn equiv(&self, other: &Self) -> Option<Vec<(TypeId, TypeId)>> {
        if self.name != other.name {
            // TODO: should this allow for one unnamed type?
            return None;
        }

        Some(vec![(self.type_id, other.type_id)])
    }
}

impl Equiv for Base {
    fn equiv(&self, other: &Self) -> Option<Vec<(TypeId, TypeId)>> {
        let self_easy = (&self.name, self.encoding, self.byte_size, self.alignment);
        let other_easy = (&other.name, other.encoding, other.byte_size, other.alignment);
        if self_easy != other_easy {
            return None;
        }

        Some(vec![])
    }
}

impl Equiv for Array {
    fn equiv(&self, other: &Self) -> Option<Vec<(TypeId, TypeId)>> {
        if self.lower_bound != other.lower_bound || self.count != other.count {
            return None;
        }

        Some(vec![
            (self.element_type_id, other.element_type_id),
            (self.index_type_id, other.index_type_id),
        ])
    }
}

impl Equiv for Enumerator {
    fn equiv(&self, other: &Self) -> Option<Vec<(TypeId, TypeId)>> {
        if self.name != other.name || self.const_value != other.const_value {
            return None;
        }
        Some(vec![])
    }
}

impl Equiv for CEnum {
    fn equiv(&self, other: &Self) -> Option<Vec<(TypeId, TypeId)>> {
        let self_easy = (&self.name, self.enum_class, self.byte_size, self.alignment);
        let other_easy = (&other.name, other.enum_class, other.byte_size, other.alignment);
        if self_easy != other_easy {
            return None;
        }

        self.enumerators.equiv(&other.enumerators)
    }
}

impl Equiv for Subroutine {
    fn equiv(&self, other: &Self) -> Option<Vec<(TypeId, TypeId)>> {
        let mut conditions = vec![];
        conditions.extend(self.return_type_id.equiv(&other.return_type_id)?);
        conditions.extend(self.formal_parameters.equiv(&other.formal_parameters)?);
        Some(conditions)
    }
}

impl Equiv for Type {
    fn equiv(&self, other: &Self) -> Option<Vec<(TypeId, TypeId)>> {
        match (self, other) {
            (Self::Struct(a), Self::Struct(b)) => a.equiv(b),
            (Self::Enum(a), Self::Enum(b)) => a.equiv(b),
            (Self::Pointer(a), Self::Pointer(b)) => a.equiv(b),
            (Self::Base(a), Self::Base(b)) => a.equiv(b),
            (Self::Array(a), Self::Array(b)) => a.equiv(b),
            (Self::CEnum(a), Self::CEnum(b)) => a.equiv(b),
            (Self::Union(a), Self::Union(b)) => a.equiv(b),
            (Self::Subroutine(a), Self::Subroutine(b)) => a.equiv(b),
            _ => None,
        }
    }
}
