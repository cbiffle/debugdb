use crate::TypeId;
use crate::model::*;
use indexmap::IndexMap;
use core::hash::Hash;
use std::collections::BTreeMap;

#[derive(Clone)]
pub struct State<'a> {
    /// Substitution map. An entry `(key, value)` in this map means that the
    /// type identified by `key` has been found to be equivalent to earlier type
    /// `value`, for canonicalization purposes.
    subs: BTreeMap<TypeId, TypeId>,

    types: &'a BTreeMap<TypeId, Type>,
}

impl<'a> State<'a> {
    pub fn new(types: &'a BTreeMap<TypeId, Type>) -> Self {
        Self {
            subs: BTreeMap::new(),
            types,
        }
    }

    pub fn merge(&mut self, other: Self) {
        for (k, v) in other.subs {
            self.equate(k, v);
        }
    }

    /// Iteratively applies substitutions to `t` until a type with no
    /// substitutions is found.
    pub fn canonicalize(&self, t: TypeId) -> TypeId {
        let mut result = t;
        while let Some(next) = self.subs.get(&result) {
            result = *next;
        }
        result
    }

    pub fn is_subbed(&self, t: TypeId) -> bool {
        self.subs.contains_key(&t)
    }

    pub fn find_type(&self, t: TypeId) -> &'a Type {
        &self.types[&self.canonicalize(t)]
    }

    pub fn finish(self) -> BTreeMap<TypeId, TypeId> {
        let mut result = BTreeMap::new();
        for &t in self.types.keys() {
            let c = self.canonicalize(t);
            // Prune.
            if c != t {
                result.insert(t, self.canonicalize(t));
            }
        }
        result
    }

    /// Unifies `a` and `b` such that they will look up to the same typeid in
    /// the future. The "canonical" type is the lower number of the two.
    ///
    /// This does no checking of similarity of `a` and `b`.
    pub fn equate(&mut self, a: TypeId, b: TypeId) {
        let ca = self.canonicalize(a);
        let cb = self.canonicalize(b);
        match ca.cmp(&cb) {
            std::cmp::Ordering::Less => {
                self.subs.insert(cb, ca);
            }
            std::cmp::Ordering::Equal => (),
            std::cmp::Ordering::Greater => {
                self.subs.insert(ca, cb);
            }
        }
    }

    fn checkpoint(&mut self, body: impl FnOnce(&mut Self) -> bool) -> bool {
        let mut cp = self.clone();
        if body(&mut cp) {
            *self = cp;
            true
        } else {
            false
        }
    }
}

pub trait Unify {
    fn try_unify(&self, other: &Self, state: &mut State<'_>) -> bool;
}

impl<T> Unify for Vec<T>
    where T: Unify,
{
    fn try_unify(&self, other: &Self, state: &mut State<'_>) -> bool {
        if self.len() != other.len() {
            return false;
        }

        state.checkpoint(|state| {
            self.iter().zip(other).all(|(a, b)| a.try_unify(b, state))
        })
    }
}

impl<T> Unify for Option<T>
    where T: Unify,
{
    fn try_unify(&self, other: &Self, state: &mut State<'_>) -> bool {
        match (self, other) {
            (Some(a), Some(b)) => a.try_unify(b, state),
            _ => false
        }
    }
}

impl<K, T> Unify for IndexMap<K, T>
    where T: Unify,
          K: Eq + Hash,
{
    fn try_unify(&self, other: &Self, state: &mut State<'_>) -> bool {
        if self.len() != other.len() {
            return false;
        }

        state.checkpoint(|state| {
            self.iter().all(|(ak, a)| a.try_unify(&other[ak], state))

        })
    }
}

impl Unify for TypeId {
    fn try_unify(&self, other: &Self, state: &mut State<'_>) -> bool {
        let cself = state.canonicalize(*self);
        let cother = state.canonicalize(*other);

        if cself == cother {
            return true;
        }

        state.checkpoint(|state| {
            // Insert a provisional substitution.
            state.equate(cself, cother);
            // Attempt recursive unification.
            state.find_type(cself).try_unify(state.find_type(cother), state)
        })
    }
}

impl Unify for Member {
    fn try_unify(&self, other: &Self, state: &mut State<'_>) -> bool {
        let self_easy = (&self.name, self.artificial, self.alignment, self.location);
        let other_easy = (&other.name, other.artificial, other.alignment, other.location);
        if self_easy != other_easy {
            return false;
        }

        self.type_id.try_unify(&other.type_id, state)
    }
}

impl Unify for Variant {
    fn try_unify(&self, other: &Self, state: &mut State<'_>) -> bool {
        self.member.try_unify(&other.member, state)
    }
}

impl Unify for VariantShape {
    fn try_unify(&self, other: &Self, state: &mut State<'_>) -> bool {
        match (self, other) {
            (Self::Zero, Self::Zero) => true,
            (Self::One(a), Self::One(b)) => a.try_unify(b, state),
            (
                Self::Many { member: ma, variants: va, .. },
                Self::Many { member: mb, variants: vb, .. },
            ) => {
                state.checkpoint(|state| {
                    ma.try_unify(mb, state)
                        && va.try_unify(vb, state)
                })
            }
            _ => false,
        }
    }
}

impl Unify for TemplateTypeParameter {
    fn try_unify(&self, other: &Self, state: &mut State<'_>) -> bool {
        if self.name != other.name {
            return false;
        }

        self.type_id.try_unify(&other.type_id, state)
    }
}

impl Unify for Struct {
    fn try_unify(&self, other: &Self, state: &mut State<'_>) -> bool {
        let self_easy = (&self.name, self.byte_size, self.alignment, self.tuple_like);
        let other_easy = (&other.name, other.byte_size, other.alignment, other.tuple_like);
        if self_easy != other_easy {
            return false;
        }

        state.checkpoint(|state| {
            self.template_type_parameters.try_unify(
                &other.template_type_parameters,
                state,
            ) && self.members.try_unify(&other.members, state)
        })
    }
}

impl Unify for Union {
    fn try_unify(&self, other: &Self, state: &mut State<'_>) -> bool {
        let self_easy = (&self.name, self.byte_size, self.alignment);
        let other_easy = (&other.name, other.byte_size, other.alignment);
        if self_easy != other_easy {
            return false;
        }

        state.checkpoint(|state| {
            self.template_type_parameters.try_unify(
                &other.template_type_parameters,
                state,
            ) && self.members.try_unify(&other.members, state)
        })
    }
}

impl Unify for Enum {
    fn try_unify(&self, other: &Self, state: &mut State<'_>) -> bool {
        let self_easy = (&self.name, self.byte_size, self.alignment);
        let other_easy = (&other.name, other.byte_size, other.alignment);
        if self_easy != other_easy {
            return false;
        }

        state.checkpoint(|state| {
            self.template_type_parameters.try_unify(
                &other.template_type_parameters,
                state,
            ) && self.shape.try_unify(&other.shape, state)
        })
    }
}

impl Unify for Pointer {
    fn try_unify(&self, other: &Self, state: &mut State<'_>) -> bool {
        if self.name != other.name {
            // TODO: should this allow for one unnamed type?
            return false;
        }

        self.type_id.try_unify(&other.type_id, state)
    }
}

impl Unify for Base {
    fn try_unify(&self, other: &Self, _state: &mut State<'_>) -> bool {
        let self_easy = (&self.name, self.encoding, self.byte_size, self.alignment);
        let other_easy = (&other.name, other.encoding, other.byte_size, other.alignment);
        self_easy == other_easy
    }
}

impl Unify for Array {
    fn try_unify(&self, other: &Self, state: &mut State<'_>) -> bool {
        if self.lower_bound != other.lower_bound || self.count != other.count {
            return false;
        }

        state.checkpoint(|state| {
            self.element_type_id.try_unify(&other.element_type_id, state)
                && self.index_type_id.try_unify(&other.index_type_id, state)
        })
    }
}

impl Unify for Enumerator {
    fn try_unify(&self, other: &Self, _state: &mut State<'_>) -> bool {
        self.name == other.name && self.const_value == other.const_value
    }
}

impl Unify for CEnum {
    fn try_unify(&self, other: &Self, state: &mut State<'_>) -> bool {
        let self_easy = (&self.name, self.enum_class, self.byte_size, self.alignment);
        let other_easy = (&other.name, other.enum_class, other.byte_size, other.alignment);
        if self_easy != other_easy {
            return false;
        }

        self.enumerators.try_unify(&other.enumerators, state)
    }
}

impl Unify for Subroutine {
    fn try_unify(&self, other: &Self, state: &mut State<'_>) -> bool {
        state.checkpoint(|state| {
            self.return_type_id.try_unify(&other.return_type_id, state)
                && self.formal_parameters.try_unify(&other.formal_parameters, state)
        })
    }
}

impl Unify for Type {
    fn try_unify(&self, other: &Self, state: &mut State<'_>) -> bool {
        match (self, other) {
            (Self::Struct(a), Self::Struct(b)) => a.try_unify(b, state),
            (Self::Enum(a), Self::Enum(b)) => a.try_unify(b, state),
            (Self::Pointer(a), Self::Pointer(b)) => a.try_unify(b, state),
            (Self::Base(a), Self::Base(b)) => a.try_unify(b, state),
            (Self::Array(a), Self::Array(b)) => a.try_unify(b, state),
            (Self::CEnum(a), Self::CEnum(b)) => a.try_unify(b, state),
            (Self::Union(a), Self::Union(b)) => a.try_unify(b, state),
            (Self::Subroutine(a), Self::Subroutine(b)) => a.try_unify(b, state),
            _ => false,
        }
    }
}
