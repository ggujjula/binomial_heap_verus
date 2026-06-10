use vstd::prelude::*;

verus! {
    #[cfg(verus_only)]
    use vstd::multiset::Multiset;
    #[cfg(verus_only)]
    use vstd::seq::Seq;

    pub open spec fn ms_add_all<T>(s: Seq<Multiset<T>>) -> Multiset<T> {
        s.fold_left(Multiset::empty(), |cv: Multiset<T>, child| cv.add(child))
    }

    proof fn lemma_ms_add_all_singleton<T>(s: Seq<Multiset<T>>)
        requires s.len() == 0,
        ensures ms_add_all(s) =~= Multiset::empty(),
    {
    }

    pub proof fn lemma_ms_add_contains<T>(s: Seq<Multiset<T>>)
        ensures forall |t: T| ms_add_all(s).contains(t) ==> (exists |i: int| 0 <= i < s.len() && #[trigger] s[i].contains(t)),
        decreases s.len(),
    {
        if s.len() == 0 {

        } else {
            let xs = s.drop_last();
            let x = s.last();
            let xs_multiset = ms_add_all(xs);
            lemma_ms_add_contains(xs);
            assert forall |t: T| ms_add_all(s).contains(t) implies (exists |i: int| 0 <= i < s.len() && #[trigger] s[i].contains(t)) by
            {
                assert(ms_add_all(s) =~= xs_multiset.add(x));
                if xs_multiset.contains(t) {
                    let i = choose |i: int| 0 <= i < xs.len() && #[trigger] xs[i].contains(t);
                    assert(0 <= i < s.len() && #[trigger] s[i].contains(t));
                } else {
                    let i = s.len() - 1;
                    assert(0 <= i < s.len() && #[trigger] s[i].contains(t));
                }
            }
        }
    }


}
