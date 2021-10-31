pub mod load;
pub mod value;

use indexmap::IndexMap;
use object::{Object, ObjectSection};
use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};
use std::num::NonZeroU64;

use gimli::constants as gim_con;

// Internal type abbreviations
type RtSlice<'a> = gimli::EndianSlice<'a, gimli::RunTimeEndian>;
type BTreeIndex<I, K> = BTreeMap<K, BTreeSet<I>>;

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

/// A database of information extracted from the debug info of a program.
///
/// This is primarily focused on correctly representing Rust programs, but it
/// can represent a large subset of C types as a side effect -- currently only
/// unnamed types present a problem. This could be fixed.
#[derive(Clone, Debug, Default)]
pub struct DebugDb {
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
    types: BTreeMap<TypeId, Type>,

    /// Index: type name to location(s) that can be looked up in `types`.
    ///
    /// Invariant: all string keys correspond to names of types in `types`.
    ///
    /// Invariant: all UnitSectionOffset values have corresponding entries in
    /// `types`.
    type_name_index: BTreeIndex<TypeId, String>,

    /// Index: array element type and size to location(s) in `types`. Since
    /// arrays do not have names in DWARF, they can't be looked up in the
    /// `type_name_index`.
    array_index: BTreeIndex<TypeId, (TypeId, Option<u64>)>,

    /// Index: subroutine argument and return types to location(s) in `types`.
    /// Since subroutine types do not have names in DWARF, they can't be looked
    /// up in the `type_name_index`.
    ///
    /// The specific structure here is a nested map: argument types -> return
    /// type -> type goffs. This allows the first lookup to happen with a slice,
    /// thanks to the `Borrow` trait, which would not be possible if the key
    /// were instead a `(Vec<Goff>, Option<Goff>)`.
    ///
    /// Note that this is subroutine _types,_ not subprograms.
    subroutine_index: BTreeMap<Vec<TypeId>, BTreeIndex<TypeId, Option<TypeId>>>,

    /// All subprograms, indexed by location in the debug section(s).
    subprograms: BTreeMap<ProgramId, Subprogram>,

    /// Mapping of text address to line number information.
    line_table: BTreeMap<u64, Vec<LineNumberRow>>,
}

impl DebugDb {
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

    /// Returns the number of types in the debug info.
    pub fn type_count(&self) -> usize {
        self.types.len()
    }

    /// Produces an iterator over all types defined in the debug info, together
    /// with their IDs.
    pub fn types(
        &self,
    ) -> impl Iterator<Item = (TypeId, &Type)> + '_ {
        self.types.iter().map(|(&id, ty)| (id, ty))
    }

    /// Looks up the type with the given ID.
    ///
    /// If you got `id` from this instance, our consistency invariant ensures
    /// that the result will be `Some`. If `id` is from another instance, or
    /// made up, you may get `None`.
    pub fn type_by_id(
        &self,
        id: TypeId,
    ) -> Option<&Type> {
        self.types.get(&id)
    }

    /// Shorthand for looking up the name of a type.
    ///
    /// Note that not all types have names, so this may return `None` even if
    /// the type exists.
    pub fn type_name(
        &self,
        id: TypeId,
    ) -> Option<Cow<'_, str>> {
        Some(self.type_by_id(id)?.name(self))
    }

    /// Consults the type-name index and returns an iterator over types with a
    /// given name.
    ///
    /// Names are matched in their entirety, e.g. the name `"Option"` does not
    /// match a type `"core::option::Option<u16>"`.
    ///
    /// Not all types are in the type name index. In particular, array types and
    /// subroutine types.
    pub fn types_by_name(
        &self,
        name: &str,
    ) -> impl Iterator<Item = (TypeId, &Type)> + '_ {
        self.consult_index(&self.type_name_index, name)
    }

    /// Consults the array index and returns an iterator over array types with a
    /// particular shape.
    pub fn array_types(
        &self,
        element: TypeId,
        count: Option<u64>,
    ) -> impl Iterator<Item = (TypeId, &Type)> + '_ {
        self.consult_index(&self.array_index, &(element, count))
    }

    /// Consults the subroutine index and returns an iterator over subroutine
    /// types with a particular shape.
    ///
    /// The return type is optional because, in both C and Rust, DWARF will omit
    /// the return type for subroutines returning `void` / `()`. As a result,
    /// looking up subroutines returning the `()` type will not produce results.
    pub fn subroutine_types(
        &self,
        argument_tys: &[TypeId],
        return_ty: Option<TypeId>,
    ) -> impl Iterator<Item = (TypeId, &Type)> + '_ {
        self.subroutine_index
            .get(argument_tys)
            .into_iter()
            .flat_map(move |index|
                self.consult_index(index, &return_ty)
            )
    }

    pub fn subprograms(
        &self,
    ) -> impl Iterator<Item = (ProgramId, &Subprogram)> + '_ {
        self.subprograms.iter().map(|(&goff, ty)| (goff, ty))
    }

    pub fn subprogram_by_id(
        &self,
        pid: ProgramId,
    ) -> Option<&Subprogram> {
        self.subprograms.get(&pid)
    }

    pub fn line_table_rows(
        &self,
    ) -> impl Iterator<Item = (u64, &[LineNumberRow])> + '_ {
        self.line_table.iter().map(|(&a, row)| (a, &**row))
    }

    pub fn lookup_line_row(
        &self,
        pc: u64,
    ) -> Option<&LineNumberRow> {
        self.line_table.range(..=pc)
            .rev()
            .flat_map(|(_, rows)| rows)
            .take_while(move |row| row.pc_range.end > pc)
            .find(move |row| row.pc_range.contains(&pc))
    }

    /// Computes the static stack slice implied by a PC value.
    ///
    /// For simple cases of subroutines without inlined code, the stack slice
    /// contains a single entry describing the subroutine and the line number
    /// within it corresponding to the PC.
    ///
    /// For more complex cases involving inlines, possibly multiple layers of
    /// inlines, the stack slice will be deeper. In this case, the last element
    /// of the returned vec is the _innermost_ inline, and the first element is
    /// the enclosing (non-inlined) subprogram.
    pub fn static_stack_for_pc(
        &self,
        pc: u64,
    ) -> Result<Vec<PcInfo>, Box<dyn std::error::Error>> {
        // Find subprogram containing PC.
        let (pid, subp) = self.subprograms()
            .find(|(_, subp)| subp.pc_range
                .as_ref()
                .map(|r| r.contains(&pc))
                .unwrap_or(false))
            .ok_or("enclosing subprogram not found")?;

        let mut frag = vec![];

        // Follow inlined subroutine tree to the tip, recording call info at
        // each step.
        let mut enclosing_prog = pid;
        let mut inlines = Some(&subp.inlines);
        'inline_loop:
            while let Some(inl) = inlines.take() {
                for inlsub in inl {
                    for pcr in &inlsub.pc_ranges {
                        if pcr.begin <= pc && pc < pcr.end {
                            // We're in this one.
                            if let Some(file) = &inlsub.call_coord.file {
                                frag.push(PcInfo {
                                    subprogram: enclosing_prog,
                                    file: file.clone(),
                                    line: inlsub.call_coord.line,
                                    column: inlsub.call_coord.column,
                                });

                                enclosing_prog = ProgramId(
                                    inlsub.abstract_origin
                                    .expect("inlined sub w/o abstract_origin")
                                );
                                inlines = Some(&inlsub.inlines);
                                continue 'inline_loop;
                            }
                        }
                    }
                }
            }

        // Finally, find the innermost record from the line number info.
        if let Some(row) = self.lookup_line_row(pc) {
            frag.push(PcInfo {
                subprogram: enclosing_prog,
                file: row.file.clone(),
                line: row.line.map(|x| x.get() as u32),
                column: row.column.map(|x| x.get() as u32),
            });
        }

        Ok(frag)
    }

    /// Looks up `key` in `index`, and then transforms the result by (1) copying
    /// the goffs and (2) attaching the associated `Type` to each item.
    fn consult_index<'d, K, Q>(
        &'d self,
        index: &'d BTreeIndex<TypeId, K>,
        key: &Q,
    ) -> impl Iterator<Item = (TypeId, &'d Type)> + 'd
        where K: std::borrow::Borrow<Q> + Ord,
              Q: Ord + ?Sized,
    {
        index
            .get(key)
            .into_iter()
            .flat_map(move |set| {
                set.iter().map(move |&goff| (goff, &self.types[&goff]))
            })
    }
}

/// Builder that accumulates the type information from a program and produces a
/// `DebugDb` database.
///
/// This is primarily intended as a write-only sink for type information. After
/// everything is stuffed in, `build()` will validate the information, generate
/// indices, and produce a `DebugDb` database.
#[derive(Clone, Debug)]
pub struct DebugDbBuilder {
    path: Vec<String>,
    endian: gimli::RunTimeEndian,
    is_64: bool,
    types: BTreeMap<TypeId, Type>,

    subprograms: BTreeMap<ProgramId, Subprogram>,
    line_table: BTreeMap<u64, Vec<LineNumberRow>>,
}

impl DebugDbBuilder {
    /// Creates a new `DebugDbBuilder` for information from a program with the
    /// given endianness and pointer width.
    pub fn new(endian: gimli::RunTimeEndian, is_64: bool) -> Self {
        Self {
            endian,
            path: vec![],
            is_64,
            types: BTreeMap::new(),
            subprograms: BTreeMap::new(),
            line_table: BTreeMap::new(),
        }
    }

    pub fn build(self) -> Result<DebugDb, Box<dyn std::error::Error>> {
        let check = |id| -> Result<(), Box<dyn std::error::Error>> {
            if self.types.contains_key(&id) {
                Ok(())
            } else {
                Err(format!("reference to missing type {:x?}", id).into())
            }
        };
        // Validate that the world is complete and internally consistent.
        for t in self.types.values() {
            match t {
                Type::Base(_) => (),
                Type::CEnum(_) => (),

                Type::Struct(s) => {
                    for ttp in &s.template_type_parameters {
                        check(ttp.type_id)?;
                    }
                    for m in s.members.values() {
                        check(m.type_id)?;
                    }
                }
                Type::Union(s) => {
                    for ttp in &s.template_type_parameters {
                        check(ttp.type_id)?;
                    }
                    for m in &s.members {
                        check(m.type_id)?;
                    }
                }
                Type::Enum(s) => {
                    for ttp in &s.template_type_parameters {
                        check(ttp.type_id)?;
                    }
                    match &s.variant_part.shape {
                        VariantShape::Zero => (),
                        VariantShape::One(variant) => {
                            check(variant.member.type_id)?;
                        }
                        VariantShape::Many {
                            member, variants, ..
                        } => {
                            check(member.type_id)?;
                            for v in variants.values() {
                                check(v.member.type_id)?;
                            }
                        }
                    }
                }
                Type::Array(s) => {
                    check(s.element_type_id)?;
                    // The index type is synthetic, but, might as well.
                    check(s.index_type_id)?;
                }
                Type::Pointer(s) => {
                    check(s.type_id)?;
                }
                Type::Subroutine(s) => {
                    if let Some(t) = s.return_type_id {
                        check(t)?;
                    }
                    for &t in &s.formal_parameters {
                        check(t)?;
                    }
                }
            }
        }

        // Build type name index.
        let type_name_index = index_by_key(&self.types, |_, t| match t {
            Type::Struct(s) => Some(s.name.clone()),
            Type::Enum(s) => Some(s.name.clone()),
            Type::Base(s) => Some(s.name.clone()),
            Type::CEnum(s) => Some(s.name.clone()),
            Type::Union(s) => Some(s.name.clone()),
            Type::Pointer(s) => Some(s.name.clone()),
            _ => None,
        });
        // Build array index.
        let array_index = index_by_key(&self.types, |_, t| match t {
            Type::Array(a) => Some((a.element_type_id, a.count)),
            _ => None,
        });
        // Build subroutine index. This is more complex in shape than the other
        // indices.
        let subroutine_index = {
            let mut ind = BTreeMap::<_, BTreeIndex<_, _>>::new();
            for (k, v) in &self.types {
                if let Type::Subroutine(s) = v {
                    ind.entry(s.formal_parameters.clone())
                        .or_default()
                        .entry(s.return_type_id)
                        .or_default()
                        .insert(*k);
                }
            }
            ind
        };

        fn check_inl(inl: &InlinedSubroutine) -> Result<(), Box<dyn std::error::Error>> {
            if inl.abstract_origin.is_none() {
                return Err(format!("inlined subroutine w/o abstract origin at {:?}", inl.offset).into());
            }
            for inner in &inl.inlines {
                check_inl(inner)?;
            }
            Ok(())
        }

        // Check that inlined subroutines match our expectations.
        for subprogram in self.subprograms.values() {
            for inl in &subprogram.inlines {
                check_inl(inl)?;
            }
        }
        Ok(DebugDb {
            endian: self.endian,
            types: self.types,
            is_64: self.is_64,
            subprograms: self.subprograms,
            line_table: self.line_table,
            type_name_index,
            array_index,
            subroutine_index,
        })
    }

    /// Adds a type to the database.
    ///
    /// It's unusual to call this from outside the library, but it might be
    /// useful if you have additional type information from some outside source.
    pub fn record_type(&mut self, t: impl Into<Type>) {
        let t = t.into();
        self.types.insert(TypeId(t.offset()), t);
    }

    pub fn record_subprogram(&mut self, t: Subprogram) {
        self.subprograms.insert(ProgramId(t.offset), t);
    }

    pub fn record_line_table_row(&mut self, addr: u64, r: LineNumberRow) {
        self.line_table.entry(addr)
            .or_default()
            .push(r)
    }

    fn format_path(&self, name: impl std::fmt::Display) -> String {
        if self.path.is_empty() {
            name.to_string()
        } else {
            format!("{}::{}", self.path.join("::"), name)
        }
    }

    /// Pushes a path component onto the namespace path stack and runs `body`,
    /// popping the stack when it completes.
    fn path_component<T>(
        &mut self,
        c: impl Into<String>,
        body: impl FnOnce(&mut Self) -> T,
    ) -> T {
        self.path.push(c.into());
        let result = body(self);
        self.path.pop();
        result
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
where
    T: Ord,
    K: Ord + Clone,
{
    let mut index: BTreeMap<T, BTreeSet<K>> = BTreeMap::new();

    for (k, v) in table {
        if let Some(i) = project(k, v) {
            index.entry(i).or_default().insert(k.clone());
        }
    }

    index
}

/// Parses type information from an `object::File`.
pub fn parse_file<'a>(
    object: &'a object::File,
) -> Result<DebugDb, Box<dyn std::error::Error>> {
    let endian = if object.is_little_endian() {
        gimli::RunTimeEndian::Little
    } else {
        gimli::RunTimeEndian::Big
    };

    let load_section =
        |id: gimli::SectionId| -> Result<Cow<'a, [u8]>, gimli::Error> {
            match object.section_by_name(id.name()) {
                Some(section) => Ok(section
                    .uncompressed_data()
                    .unwrap_or(Default::default())),
                None => Ok(Default::default()),
            }
        };

    let dwarf_cow = gimli::Dwarf::load(&load_section)?;

    let dwarf =
        dwarf_cow.borrow(|section| gimli::EndianSlice::new(section, endian));

    let mut iter = dwarf.units();
    let mut builder = DebugDbBuilder::new(endian, object.is_64());

    while let Some(header) = iter.next()? {
        let unit = dwarf.unit(header)?;

        if let Some(lp) = &unit.line_program {
            let lp = lp.clone();
            let mut rows = lp.rows();

            let mut last_row: Option<LineNumberRow> = None;
            while let Some((header, row)) = rows.next_row()? {
                let file = if let Some(file) = row.file(header) {
                    if let Some(directory) = file.directory(header) {
                        format!(
                            "{}/{}",
                            dwarf.attr_string(&unit, directory)?.to_string_lossy(),
                            dwarf
                            .attr_string(&unit, file.path_name())?
                            .to_string_lossy()
                        ).into()
                    } else {
                        dwarf
                            .attr_string(&unit, file.path_name())?
                            .to_string_lossy()
                    }
                } else {
                    "???".into()
                };
                if let Some(mut pending) = last_row.take() {
                    pending.pc_range.end = row.address();
                    builder.record_line_table_row(pending.pc_range.start, pending);
                }

                if !row.end_sequence() {
                    last_row = Some(LineNumberRow {
                        pc_range: row.address()..0,
                        file: file.into_owned(),
                        line: row.line(),
                        column: match row.column() {
                            gimli::ColumnType::Column(c) => Some(c),
                            gimli::ColumnType::LeftEdge => None,
                        },
                    });
                }
            }
            if last_row.is_some() {
                eprintln!("WARN: line number program not terminated by end sequence");
            }
        }
        let mut entries = unit.entries();
        while let Some(()) = entries.next_entry()? {
            if entries.current().is_none() {
                break;
            }
            parse_entry(&dwarf, &unit, &mut entries, &mut builder)?;
        }
    }

    builder.build()
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
            _ => {
                skip_entry(cursor)?;
            }
        }
    }

    Ok(())
}

fn parse_entry(
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

#[derive(Clone, Debug)]
pub struct Base {
    pub name: String,
    pub encoding: Encoding,
    pub byte_size: u64,
    pub offset: gimli::UnitSectionOffset,
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

#[derive(Debug, Clone)]
pub struct Struct {
    pub name: String,
    pub byte_size: u64,
    pub alignment: Option<u64>,
    pub template_type_parameters: Vec<TemplateTypeParameter>,
    pub tuple_like: bool,
    pub members: IndexMap<String, Member>,
    pub offset: gimli::UnitSectionOffset,
}

#[derive(Debug, Clone)]
pub struct Enum {
    pub name: String,
    pub byte_size: u64,
    pub alignment: Option<u64>,
    pub template_type_parameters: Vec<TemplateTypeParameter>,
    pub variant_part: VariantPart,
    pub offset: gimli::UnitSectionOffset,
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
        }
    }

    pub fn alignment(&self, world: &DebugDb) -> Option<u64> {
        match self {
            Self::Struct(s) => s.alignment,
            Self::Enum(s) => s.alignment,
            Self::Base(s) => {
                // TODO: we're going to just assume that all base types are
                // naturally aligned.
                Some(s.byte_size)
            }
            Self::CEnum(s) => Some(s.alignment),
            Self::Union(s) => Some(s.alignment),
            Self::Array(a) => {
                let eltty = world.type_by_id(a.element_type_id)?;
                eltty.alignment(world)
            }
            Self::Pointer(_) => Some(world.pointer_size()),
            Self::Subroutine(_) => None,
        }
    }

    pub fn byte_size(&self, world: &DebugDb) -> Option<u64> {
        match self {
            Self::Struct(s) => Some(s.byte_size),
            Self::Enum(s) => Some(s.byte_size),
            Self::Base(s) => Some(s.byte_size),
            Self::CEnum(s) => Some(s.byte_size),
            Self::Union(s) => Some(s.byte_size),
            Self::Array(a) => {
                let eltty = world.type_by_id(a.element_type_id)?;
                let eltsize = eltty.byte_size(world)?;
                Some(a.count? * eltsize)
            }
            Self::Pointer(_) => Some(world.pointer_size()),
            Self::Subroutine(_) => None,
        }
    }

    pub fn name(&self, world: &DebugDb) -> Cow<'_, str> {
        match self {
            Self::Struct(s) => (&s.name).into(),
            Self::Enum(s) => (&s.name).into(),
            Self::Base(s) => (&s.name).into(),
            Self::CEnum(s) => (&s.name).into(),
            Self::Union(s) => (&s.name).into(),
            Self::Pointer(s) => (&s.name).into(),
            Self::Array(a) => {
                let eltname = world
                    .type_by_id(a.element_type_id.into())
                    .map(|t| t.name(world))
                    .unwrap_or("???".into());

                if let Some(n) = a.count {
                    format!("[{}; {}]", eltname, n).into()
                } else {
                    format!("[{}; ???]", eltname).into()
                }
            }
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
        panic!(
            "expected 1 variant part at most, found {}",
            variant_parts.len()
        );
    }
    Ok(())
}

#[derive(Debug, Clone)]
pub struct TemplateTypeParameter {
    pub name: String,
    pub type_id: TypeId,
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

#[derive(Debug, Clone)]
pub struct Member {
    pub name: Option<String>,
    pub artificial: bool,
    pub type_id: TypeId,
    pub alignment: Option<u64>,
    pub location: u64,
    pub offset: gimli::UnitSectionOffset,
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

#[derive(Debug, Clone)]
pub struct VariantPart {
    pub offset: gimli::UnitSectionOffset,
    pub shape: VariantShape,
}

#[derive(Debug, Clone)]
pub enum VariantShape {
    Zero,
    One(Variant),
    Many {
        discr: gimli::UnitSectionOffset,
        member: Member,
        variants: IndexMap<Option<u64>, Variant>,
    },
}

fn parse_variant_part(
    dwarf: &gimli::Dwarf<RtSlice<'_>>,
    unit: &gimli::Unit<RtSlice<'_>>,
    cursor: &mut gimli::EntriesCursor<'_, '_, RtSlice<'_>>,
) -> Result<VariantPart, Box<dyn std::error::Error>> {
    let entry = cursor.current().unwrap();
    assert!(entry.tag() == gim_con::DW_TAG_variant_part);

    let offset = entry.offset().to_unit_section_offset(unit);
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
    Ok(VariantPart { shape, offset })
}

#[derive(Debug, Clone)]
pub struct Variant {
    pub member: Member,
    pub offset: gimli::UnitSectionOffset,
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

#[derive(Debug, Clone)]
pub struct CEnum {
    pub name: String,
    pub enum_class: bool,
    pub byte_size: u64,
    pub alignment: u64,
    pub enumerators: IndexMap<u64, Enumerator>,
    pub offset: gimli::UnitSectionOffset,
}

#[derive(Debug, Clone)]
pub struct Enumerator {
    pub name: String,
    pub const_value: u64,
    pub offset: gimli::UnitSectionOffset,
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

#[derive(Debug, Clone)]
pub struct Array {
    pub element_type_id: TypeId,
    pub index_type_id: TypeId,
    pub lower_bound: u64,
    pub count: Option<u64>,
    pub offset: gimli::UnitSectionOffset,
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

#[derive(Debug, Clone)]
pub struct Pointer {
    pub type_id: TypeId,
    pub name: String,
    pub offset: gimli::UnitSectionOffset,
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

#[derive(Debug, Clone)]
pub struct Union {
    pub name: String,
    pub byte_size: u64,
    pub alignment: u64,
    pub template_type_parameters: Vec<TemplateTypeParameter>,
    pub members: Vec<Member>,
    pub offset: gimli::UnitSectionOffset,
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

#[derive(Clone, Debug)]
pub struct Subroutine {
    pub return_type_id: Option<TypeId>,
    pub formal_parameters: Vec<TypeId>,
    pub offset: gimli::UnitSectionOffset,
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
                decl_coord.line = Some(attr.value().udata_value().unwrap() as u32);
            }
            gim_con::DW_AT_decl_column => {
                decl_coord.column = Some(attr.value().udata_value().unwrap() as u32);
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

#[derive(Clone, Debug)]
pub struct Subprogram {
    pub offset: gimli::UnitSectionOffset,
    pub name: Option<String>,
    pub pc_range: Option<std::ops::Range<u64>>,
    pub decl_coord: DeclCoord,
    pub return_type_id: Option<TypeId>,
    pub formal_parameters: Vec<SubParameter>,
    pub template_type_parameters: Vec<TemplateTypeParameter>,
    pub inlines: Vec<InlinedSubroutine>,
    pub abstract_origin: Option<gimli::UnitSectionOffset>,
    pub linkage_name: Option<String>,
    pub noreturn: bool,
}

#[derive(Clone, Debug)]
pub struct SubParameter {
    pub offset: gimli::UnitSectionOffset,
    pub name: Option<String>,
    pub decl_coord: DeclCoord,
    pub type_id: Option<TypeId>,
    pub abstract_origin: Option<gimli::UnitSectionOffset>,
}

#[derive(Clone, Debug, Default)]
pub struct DeclCoord {
    pub file: Option<String>,
    pub line: Option<u32>,
    pub column: Option<u32>,
}

#[derive(Clone, Debug)]
pub struct InlinedSubroutine {
    pub offset: gimli::UnitSectionOffset,
    pub abstract_origin: Option<gimli::UnitSectionOffset>,
    pub pc_ranges: Vec<gimli::Range>,
    pub call_coord: DeclCoord,
    pub inlines: Vec<InlinedSubroutine>,
    pub formal_parameters: Vec<SubParameter>,
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
                decl_coord.line = Some(attr.value().udata_value().unwrap() as u32);
            }
            gim_con::DW_AT_decl_column => {
                decl_coord.column = Some(attr.value().udata_value().unwrap() as u32);
            }
            // const_value
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
                call_coord.line = Some(attr.value().udata_value().unwrap() as u32);
            }
            gim_con::DW_AT_call_column => {
                call_coord.column = Some(attr.value().udata_value().unwrap() as u32);
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

#[derive(Clone, Debug)]
pub struct LineNumberRow {
    pub pc_range: std::ops::Range<u64>,
    pub file: String,
    pub line: Option<NonZeroU64>,
    pub column: Option<NonZeroU64>,
}

pub struct PcInfo {
    pub subprogram: ProgramId,
    pub file: String,
    pub line: Option<u32>,
    pub column: Option<u32>,
}
