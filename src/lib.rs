//mod scratch;
pub mod tree;
mod union;

use crate::tree::BinomialTree as InnerTree;
//use std::fmt::Debug;
#[cfg(verus_only)]
use verus_relations::proven_ord::proven_ord::group_proven_ord;
use verus_relations::proven_ord::proven_ord::ProvenOrd;
#[cfg(verus_only)]
use verus_relations::proven_partialord::proven_partialord::group_proven_partialord;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::std_specs::cmp::*;

verus! {

    broadcast use {group_proven_partialord, group_proven_ord};

    pub struct BinomialHeap<'a, T: ProvenOrd> {
        trees: Vec<InnerTree<T>>,
        cache: Option<&'a T>,
    }

    impl <T: ProvenOrd> Default for  BinomialHeap<'_, T> {
        fn default() -> Self {
            Self::new()
        }
    }

    impl <'a, T: ProvenOrd> BinomialHeap<'a, T> {
        pub closed spec fn contains(&self, t: T) -> bool {
            exists |i: int| 0 <= i < self.trees@.len() && (#[trigger] self.trees@[i])@.contains(t)
        }

        pub closed spec fn is_empty(&self) -> bool {
            self.size() == 0
        }

        pub closed spec fn size(self) -> nat {
            self.trees@.fold_left(0nat, |size: nat, tree: InnerTree<T>| size + tree.size())
        }

        pub closed spec fn cache_wf(&self) -> bool {
            match self.cache {
                None => true,
                Some(min) => {
                    &&& self.contains(*min)
                    &&& forall |t: T| self.contains(t) ==> min.is_le(&t)
                }
            }
        }

        #[verifier::type_invariant]
        closed spec fn wf(&self) -> bool {
            &&& forall |i: int, j: int| #![trigger self.trees@[i], self.trees@[j]]
                0 <= i < j < self.trees@.len() ==> self.trees@[i].spec_rank() < self.trees[j].spec_rank()
            &&& self.cache_wf()
        }

        pub fn new() -> Self {
            Self {
                trees: vec![],
                cache: None,
            }
        }

        pub fn push(&mut self, t: T)
            ensures final(self).size() == old(self).size() + 1
        {
            let tree = InnerTree::new(t);
            //TODO
            proof {
                assume(false)
            }
        }

        pub fn pop(&mut self) -> (ret: Option<T>)
            ensures match ret {
                None => final(self).is_empty(),
                Some(min) => {
                    &&& final(self).size() == old(self).size() - 1
                    &&& (forall |t: T| final(self).contains(t) ==> min.is_le(&t))
                }
            }
        {
            proof {
                use_type_invariant(&*self);
            }
            if self.trees.is_empty() {
                return None;
            }
            //TODO
            proof {
                assume(false)
            }
            None
        }

        pub fn peek(&'a mut self) -> (ret: Option<&'a T>)
            ensures match ret {
                None => final(self).is_empty(),
                Some(min) => forall |t: T| final(self).contains(t) ==> min.is_le(&t)
        }
        {
            proof {
                use_type_invariant(&*self);
            }
            if let Some(min) = self.cache {
                return Some(min);
            }
            if self.trees.is_empty() {
                return None;
            }
            let mut min = self.trees[0].peek();
            for i in 1..self.trees.len()
                invariant
                    1 <= i <= self.trees@.len(),
                    forall |j : int| #![trigger self.trees@[j]] 0 <= j < i ==> (forall |t: T| self.trees@[j]@.contains(t) ==> min.is_le(&t)),
                    self.contains(*min),
            {
                let peek = self.trees[i].peek();
                if peek < min {
                    min = peek;
                }
            }
            self.cache = Some(min);
            self.cache
        }
    }
}
