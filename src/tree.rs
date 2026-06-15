use vstd::prelude::*;

verus! {
    #[cfg(verus_only)]
    use verus_relations::proven_ord::proven_ord::group_proven_ord;
    use verus_relations::proven_ord::proven_ord::ProvenOrd;
    #[cfg(verus_only)]
    use verus_relations::proven_partialord::proven_partialord::group_proven_partialord;
    use vstd::multiset::Multiset;
    #[cfg(verus_only)]
    use vstd::std_specs::cmp::*;
    use vstd::view::View;
    #[cfg(verus_only)]
    use crate::union::{ms_add_all, lemma_ms_add_all_adds, lemma_ms_add_contains};

    broadcast use {group_proven_partialord, group_proven_ord};

    pub struct BinomialTree<T: ProvenOrd> {
        element: T,
        children: Vec<BinomialTree<T>>,
    }

    impl<T: ProvenOrd> View for BinomialTree<T> {
        type V = Multiset<T>;

        closed spec fn view(&self) -> Self::V
            decreases self, 1int
        {
            ms_add_all(self.inner_view()).insert(self.element)
        }
    }

    impl<T: ProvenOrd> BinomialTree<T> {

        pub closed spec fn size(&self) -> nat {
            self@.len()
        }

        closed spec fn inner_view(&self) -> Seq<Multiset<T>>
            decreases self, 0int
        {
            let child_fn = |i: int, child: BinomialTree<T>| {
                if 0 <= i < self.children@.len() {
                    self.children[i].view()
                } else {
                    arbitrary()
                }};
            self.children@.map(child_fn)
        }


        #[verifier::type_invariant]
        pub closed spec fn well_formed(self) -> bool
            decreases self
        {
            &&& forall |i: int| 0 <= i < self.children@.len() ==> self.spec_rank() > #[trigger] self.children[i].spec_rank()
            &&& forall |i: int| 0 <= i < self.children@.len() ==> self.element.is_le(#[trigger] &self.children[i].element)
            &&& forall |i: int| 0 <= i < self.children@.len() ==> (#[trigger] self.children[i]).well_formed()
            &&& forall |i: int, j: int| 0 <= i < j < self.children.len() ==> #[trigger] self.children[i].spec_rank() < #[trigger] self.children[j].spec_rank()
        }

        proof fn lemma_min_at_root(&self)
            requires self.well_formed(),
            ensures forall |t: T| self.view().contains(t) ==> self.element.is_le(&t),
            decreases self
        {
            if self.spec_rank() == 0 {
                return;
            }
            reveal(BinomialTree::inner_view);
            let child_fn = |i: int, child: BinomialTree<T>| {
                if 0 <= i < self.children@.len() {
                    self.children[i].view()
                } else {
                    arbitrary()
                }};
            assert(self.inner_view() == self.children@.map(child_fn));
            assert forall |i: int| #![trigger self.children[i]] (0 <= i < self.children@.len()) implies (forall |t: T| (self.children[i].view().contains(t)) ==> self.element.is_le(&t))
                by {
                    self.children[i].lemma_min_at_root();
                }
            lemma_ms_add_contains(self.inner_view());
            assert(forall |t: T| ms_add_all(self.inner_view()).contains(t) ==> self.element.is_le(&t));
            assert forall |t: T| self.view().contains(t) implies self.element.is_le(&t) by
            {
                assert(self.view() =~= ms_add_all(self.inner_view()).insert(self.element));
                if ms_add_all(self.inner_view()).contains(t) {
                    assert(forall |t: T| ms_add_all(self.inner_view()).contains(t) ==> self.element.is_le(&t));
                } else {
                    assert(t == self.element);
                    assert(self.element.is_le(&self.element));
                }

            }
        }

        pub fn new(elem: T) -> Self {
            Self {
                element: elem,
                children: vec![],
            }
        }

        pub closed spec fn spec_rank(&self) -> nat {
            self.children@.len()
        }

        pub fn rank(&self) -> usize {
            self.children.len()
        }

        pub fn link(first: Self, other: Self) -> (ret: Self)
            requires first.spec_rank() == other.spec_rank(),
            ensures ret@ =~= first@.add(other@),
        {
            proof {
                use_type_invariant(&first);
                use_type_invariant(&other);
            }
            let (lower, higher) = match first.element.cmp(&other.element) {
                std::cmp::Ordering::Less | std::cmp::Ordering::Equal => (first, other),
                std::cmp::Ordering::Greater => (other, first),
            };
            let ghost old_lower = lower;
            let retval = Self {
                element: lower.element,
                children: {
                    let mut new_children = lower.children;
                    new_children.push(higher);
                    new_children
                }
            };
            proof {
                lemma_ms_add_all_adds(old_lower.inner_view(), higher@);
                assert(old_lower.inner_view().push(higher@) =~= retval.inner_view());
            }
            retval
        }

        pub fn peek(&self) -> (retval: &T)
            ensures
                self@.contains(*retval),
                forall |t: T| self.view().contains(t) ==> retval.is_le(&t),
        {
            proof {
                use_type_invariant(&self);
                self.lemma_min_at_root();
            }
            &self.element
        }
    }
} // verus!
