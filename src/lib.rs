//! Collects debug information from a program into a queryable, cross-referenced
//! form.

pub mod load;
pub mod value;
pub mod model;
pub mod unify;

mod dwarf_parser;

use crate::unify::Unify;
use crate::dwarf_parser::ParseError;

pub use self::model::*;

use object::{Object, ObjectSection, ObjectSymbol};
use thiserror::Error;
use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};
use std::convert::Infallible;
use std::sync::Arc;

// Internal type abbreviations
type BTreeIndex<I, K> = BTreeMap<K, BTreeSet<I>>;
type RtArcReader = gimli::EndianReader<gimli::RunTimeEndian, Arc<[u8]>>;

/// A database of information extracted from the debug info of a program.
///
/// This is primarily focused on correctly representing Rust programs, but it
/// can represent a large subset of C types as a side effect -- currently only
/// unnamed types present a problem. This could be fixed.
#[derive(Clone, Debug)]
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

    /// Type canonicalization relationships. If a type ID is present as a key in
    /// this map, then it is _not_ the canonical instance of its type, and
    /// should be replaced by the corresponding value in the map for analysis
    /// purposes.
    type_canon: BTreeMap<TypeId, TypeId>,

    /// Reverse type canonicalization relationship. Each key in this map is the
    /// ID of a canonical instance of a family of types, and the value lists
    /// those types.
    type_rcanon: BTreeMap<TypeId, BTreeSet<TypeId>>,

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

    /// All static variables, indexed by ID.
    variables: BTreeMap<VarId, StaticVariable>,

    /// Index: static variables by name.
    variables_by_name: BTreeIndex<VarId, String>,

    /// All entities with fixed addresses, indexed by base address.
    entities_by_address: BTreeMap<u64, Vec<AddressRange>>,

    // TODO
    pub debug_frame: gimli::DebugFrame<gimli::EndianReader<gimli::RunTimeEndian, Arc<[u8]>>>,

    raw_symbols_by_address: BTreeMap<u64, BTreeSet<String>>,
    raw_symbols_by_name: BTreeMap<String, BTreeSet<u64>>,
}

impl DebugDb {
    /// Gets the endianness of the program.
    pub fn endian(&self) -> gimli::RunTimeEndian {
        self.endian
    }

    /// Gets the size of a pointer in the program, in bytes.
    pub fn pointer_size(&self) -> usize {
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

    /// Produces an iterator over all canonical types defined in the debug info,
    /// together with their IDs.
    pub fn canonical_types(
        &self,
    ) -> impl Iterator<Item = (TypeId, &Type)> + '_ {
        self.types()
            .filter(move |(tid, _t)| !self.type_canon.contains_key(tid))
    }

    pub fn aliases_of_type(&self, id: TypeId) -> Option<&BTreeSet<TypeId>> {
        self.type_rcanon.get(&id)
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

    /// Returns an iterator over all subprograms defined in this program.
    pub fn subprograms(
        &self,
    ) -> impl Iterator<Item = (ProgramId, &Subprogram)> + '_ {
        self.subprograms.iter().map(|(&goff, ty)| (goff, ty))
    }

    /// Looks up a subprogram given its `ProgramId`.
    pub fn subprogram_by_id(
        &self,
        pid: ProgramId,
    ) -> Option<&Subprogram> {
        self.subprograms.get(&pid)
    }

    /// Returns an iterator over _all_ rows in the computed line number table.
    ///
    /// You probably don't want to do this.
    pub fn line_table_rows(
        &self,
    ) -> impl Iterator<Item = (u64, &[LineNumberRow])> + '_ {
        self.line_table.iter().map(|(&a, row)| (a, &**row))
    }

    /// Looks up the line number table entry associated with `pc`.
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
    ) -> Result<Option<Vec<PcInfo>>, ParseError> {
        // Find subprogram containing PC.
        let Some((pid, subp)) = self.subprograms()
            .find(|(_, subp)| subp.pc_range
                .as_ref()
                .map(|r| r.contains(&pc))
                .unwrap_or(false))
            else { return Ok(None); };

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
                line: row.line,
                column: row.column,
            });
        }

        Ok(Some(frag))
    }

    pub fn unique_raw_symbol_by_name(
        &self,
        name: &str,
    ) -> Option<u64> {
        let addresses = self.raw_symbols_by_name.get(name)?;
        let mut i = addresses.iter().cloned();
        let result = i.next()?;
        if i.next().is_some() {
            None
        } else {
            Some(result)
        }
    }

    pub fn raw_symbols_for_address(
        &self,
        address: u64,
    ) -> impl Iterator<Item = &str> {
        self.raw_symbols_by_address.get(&address)
            .into_iter()
            .flat_map(|set| set.iter().map(String::as_str))
    }

    /// Returns an iterator over all static variables defined in this program.
    pub fn static_variables(
        &self,
    ) -> impl Iterator<Item = (VarId, &StaticVariable)> + '_ {
        self.variables.iter().map(|(&goff, ty)| (goff, ty))
    }

    pub fn static_variable_by_id(
        &self,
        id: VarId,
    ) -> Option<&StaticVariable> {
        self.variables.get(&id)
    }

    pub fn static_variables_by_name(
        &self,
        name: &str,
    ) -> impl Iterator<Item = (VarId, &StaticVariable)> + '_ {
        self.consult_index_generic(&self.variables_by_name, name, &self.variables)
    }

    pub fn unique_static_variable_by_name(
        &self,
        name: &str,
    ) -> Option<(VarId, &StaticVariable)> {
        let mut vs = self.static_variables_by_name(name);
        let result = vs.next()?;
        if vs.next().is_some() {
            None
        } else {
            Some(result)
        }
    }

    pub fn entities_by_address(
        &self,
        address: u64,
    ) -> impl Iterator<Item = &AddressRange> + '_ {
        self.entities_by_address.range(..=address)
            .rev()
            .flat_map(|(_, rec)| rec)
            .filter(move |rec| rec.range.contains(&address))
    }

    /// Looks up `key` in `index`, and then transforms the result by (1) copying
    /// the goffs and (2) attaching the associated `Type` to each item.
    fn consult_index<'d, K, Q>(
        &'d self,
        index: &'d BTreeIndex<TypeId, K>,
        key: &Q,
    ) -> impl Iterator<Item = (TypeId, &'d Type)> + 'd
        where K: std::borrow::Borrow<Q> + Ord,
              Q: Ord + ?Sized + 'd,
    {
        self.consult_index_generic(index, key, &self.types)
    }

    /// Looks up `key` in `index`, and then transforms the result by (1) copying
    /// the goffs and (2) attaching the associated `Type` to each item.
    fn consult_index_generic<'d, I, K, Q, E>(
        &'d self,
        index: &'d BTreeIndex<I, K>,
        key: &Q,
        lookup: &'d BTreeMap<I, E>,
    ) -> impl Iterator<Item = (I, &'d E)> + 'd
        where K: std::borrow::Borrow<Q> + Ord,
              Q: Ord + ?Sized,
              I: Copy + Eq + Ord,
              E: 'd,
    {
        index
            .get(key)
            .into_iter()
            .flat_map(move |set| {
                set.iter().map(move |&goff| (goff, &lookup[&goff]))
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
    decls: BTreeMap<String, BTreeSet<TypeId>>,
    debug_frame: gimli::DebugFrame<gimli::EndianReader<gimli::RunTimeEndian, Arc<[u8]>>>,

    subprograms: BTreeMap<ProgramId, Subprogram>,
    line_table: BTreeMap<u64, Vec<LineNumberRow>>,
    variables: BTreeMap<VarId, StaticVariable>,

    raw_symbols: Vec<(String, u64)>,
}

impl DebugDbBuilder {
    /// Creates a new `DebugDbBuilder` for information from a program with the
    /// given endianness and pointer width.
    pub fn new(
        endian: gimli::RunTimeEndian,
        is_64: bool,
        debug_frame: gimli::DebugFrame<gimli::EndianReader<gimli::RunTimeEndian, Arc<[u8]>>>,
    ) -> Self {
        Self {
            endian,
            path: vec![],
            is_64,
            debug_frame,
            types: BTreeMap::new(),
            decls: BTreeMap::new(),
            subprograms: BTreeMap::new(),
            line_table: BTreeMap::new(),
            variables: BTreeMap::new(),
            raw_symbols: vec![],
        }
    }

    pub fn build(self) -> Result<DebugDb, ParseError> {
        let mut types = self.types;

        // Build type name index.
        let mut type_name_index = index_by_key(&types, |_, t| match t {
            Type::Struct(s) => Some(s.name.clone()),
            Type::Enum(s) => Some(s.name.clone()),
            Type::Base(s) => Some(s.name.clone()),
            Type::CEnum(s) => Some(s.name.clone()),
            Type::Union(s) => Some(s.name.clone()),
            Type::Pointer(s) => s.name.clone(),
            _ => None,
        });

        // Attempt to unify similarly named types, narrowing the type name index
        // as we go.
        let mut u = crate::unify::State::new(&types);
        for (_name, homonyms) in &mut type_name_index {
            let mut workset = homonyms.clone();
            let mut group_u = crate::unify::State::new(&types);
            while let Some(t) = workset.pop_first() {
                for o in &workset {
                    t.try_unify(o, &mut group_u);
                }
            }
            // Reduce the set of homonyms for this name to only those types that
            // were not found to have equivalent partners.
            homonyms.retain(|t| !group_u.is_subbed(*t));
            u.merge(group_u);
        }

        // Attempt to resolve decls.
        let mut ambiguous_decl_count = 0;
        for (name, decl_ids) in &self.decls {
            if let Some(tids) = type_name_index.get(name) {
                if tids.len() != 1 {
                    // The name is still ambiguous after unification.
                    eprintln!("WARN: decl ambiguous; {name} could be:");
                    for tid in tids {
                        eprintln!("- {tid:x?}");
                    }
                    ambiguous_decl_count += 1;
                }
                // Assume it's the first one.
                let tid = *tids.iter().next().unwrap();
                for &alias in decl_ids {
                    u.equate(alias, tid);
                }
            } else {
                eprintln!("WARN: unresolved declaration {name}:");
                for id in decl_ids {
                    eprintln!(" - {id:x?}");
                }
            }
        }
        if ambiguous_decl_count > 0 {
            eprintln!("WARN: {ambiguous_decl_count} ambiguous declarations found");
        }

        let mut unresolved_types = BTreeMap::new();

        let mut check = |mut id| -> Result<(), Infallible> {
            id = u.canonicalize(id);
            if types.contains_key(&id) {
                Ok(())
            } else {
                unresolved_types.insert(id, Type::Unresolved(Unresolved {
                    offset: id.0,
                }));
                Ok(()) // TODO
            }
        };
        
        // Validate that the world is complete and internally consistent.
        for t in types.values() {
            match t {
                Type::Base(_) => (),
                Type::CEnum(_) => (),
                Type::Unresolved(_) => (),

                Type::Struct(s) => {
                    for ttp in &s.template_type_parameters {
                        check(ttp.type_id)?;
                    }
                    for m in &s.members {
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
                    match &s.shape {
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

        let type_canon = u.finish();
        types.extend(unresolved_types);

        // Build array index.
        let array_index = index_by_key(&types, |_, t| match t {
            Type::Array(a) => Some((a.element_type_id, a.count)),
            _ => None,
        });
        // Build subroutine index. This is more complex in shape than the other
        // indices.
        let subroutine_index = {
            let mut ind = BTreeMap::<_, BTreeIndex<_, _>>::new();
            for (k, v) in &types {
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

        let variables_by_name = index_by_key(&self.variables, |_, v| Some(v.name.clone()));

        // Build address map.
        let mut entities_by_address: BTreeMap<_, Vec<_>> = BTreeMap::new();
        for (&vid, v) in &self.variables {
            let Some(t) = types.get(&v.type_id) else {
                eprintln!("WARN: type of variable {} not found: {:x?}",
                    v.name, v.type_id);
                continue;
            };
            let sz = t.byte_size_early(
                if self.is_64 { 8 } else { 4 },
                |t| types.get(&t),
            );
            if let Some(sz) = sz {
                entities_by_address.entry(v.location)
                    .or_default()
                    .push(AddressRange {
                        range: v.location..v.location + sz,
                        entity: EntityId::Var(vid),
                    });
            }
        }
        for (&pid, p) in &self.subprograms {
            if let Some(pc_range) = p.pc_range.clone() {
                entities_by_address.entry(pc_range.start)
                    .or_default()
                    .push(AddressRange {
                        range: pc_range,
                        entity: EntityId::Prog(pid),
                    });
            }
        }

        fn check_inl(inl: &InlinedSubroutine) -> Result<(), ParseError> {
            if inl.abstract_origin.is_none() {
                return Err(ParseError::UnboundSubroutine(inl.offset));
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

        let type_rcanon = invert(&type_canon);

        let raw_symbols_by_name = index_by_key(
            self.raw_symbols.iter().map(|(k, v)| (v, k)),
            |_, name| Some(name.to_string()),
        );

        let raw_symbols_by_address = index_by_key(
            self.raw_symbols.iter().map(|(k, v)| (k, v)),
            |_, addr| Some(*addr),
        );


        Ok(DebugDb {
            endian: self.endian,
            types,
            type_canon,
            type_rcanon,
            is_64: self.is_64,
            subprograms: self.subprograms,
            line_table: self.line_table,
            variables: self.variables,
            debug_frame: self.debug_frame,
            type_name_index,
            array_index,
            subroutine_index,
            variables_by_name,
            entities_by_address,
            raw_symbols_by_name,
            raw_symbols_by_address,
        })
    }

    pub fn record_raw_symbol(&mut self, addr: u64, name: String) {
        self.raw_symbols.push((name, addr));
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

    pub fn record_variable(&mut self, t: StaticVariable) {
        self.variables.insert(VarId(t.offset), t);
    }

    pub fn record_line_table_row(&mut self, addr: u64, r: LineNumberRow) {
        self.line_table.entry(addr)
            .or_default()
            .push(r)
    }

    pub fn record_decl(&mut self, name: impl std::fmt::Display, id: TypeId) {
        self.decls.entry(self.format_path(name))
            .or_default()
            .insert(id);
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

#[derive(Clone, Debug, Error)]
pub enum FileError {
    #[error("DWARF data structures could not be understood")]
    Parse(#[from] ParseError),
    #[error("Object file format parsing error")]
    Obj(#[from] object::Error),
    #[error("DWARF failed to parse")]
    Dwarf(#[from] gimli::Error),
}

/// Parses type information from an `object::File`.
pub fn parse_file<'a>(
    object: &'a object::File,
) -> Result<DebugDb, FileError> {
    let endian = if object.is_little_endian() {
        gimli::RunTimeEndian::Little
    } else {
        gimli::RunTimeEndian::Big
    };

    let load_section =
        |id: gimli::SectionId| -> Result<RtArcReader, FileError> {
            let cow = object.section_by_name(id.name())
                .map(|sect| sect.uncompressed_data())
                .transpose()?
                .unwrap_or_else(Default::default);
            Ok(gimli::EndianReader::new(Arc::from(cow), endian))
        };

    let dwarf = gimli::Dwarf::load(&load_section)?;

    use gimli::Section;
    let debug_frame = gimli::DebugFrame::load(load_section)?;

    let mut builder = DebugDbBuilder::new(endian, object.is_64(), debug_frame);

    let mut iter = dwarf.units();
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
                            String::from_utf8_lossy(dwarf.attr_string(&unit, directory)?.bytes()),
                            String::from_utf8_lossy(
                            dwarf
                            .attr_string(&unit, file.path_name())?
                            .bytes())
                        ).into()
                    } else {
                        String::from_utf8_lossy(
                        dwarf
                            .attr_string(&unit, file.path_name())?
                            .bytes())
                            .into_owned()
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
                        file,
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
            dwarf_parser::parse_entry(&dwarf, &unit, &mut entries, &mut builder)?;
        }
    }

    for sym in object.symbols() {
        let Ok(name) = sym.name() else { continue; };
        let addr = sym.address();
        builder.record_raw_symbol(addr, name.to_string());
    }

    Ok(builder.build()?)
}

#[derive(Clone, Debug)]
pub struct AddressRange {
    pub range: std::ops::Range<u64>,
    pub entity: EntityId,
}

#[derive(Copy, Clone, Debug)]
pub enum EntityId {
    Var(VarId),
    Prog(ProgramId),
}

fn invert<K, V>(map: &BTreeMap<K, V>) -> BTreeMap<V, BTreeSet<K>>
    where K: Eq + Ord + Clone,
          V: Eq + Ord + Clone,
{
    let mut result: BTreeMap<V, BTreeSet<K>> = BTreeMap::new();
    for (k, v) in map {
        result.entry(v.clone()).or_default().insert(k.clone());
    }
    result
}
