use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn xor_fold(s: Seq<i32>) -> i32
        decreases s.len(),
    {
        if s.len() == 0 {
            0
        } else {
            Self::xor_fold(s.drop_last()) ^ s.last()
        }
    }

    pub open spec fn range_xor(arr: Seq<i32>, l: int, r: int) -> i32
        recommends
            0 <= l <= r < arr.len(),
    {
        Self::xor_fold(arr.subrange(l, r + 1))
    }

    proof fn lemma_xor_fold_push(s: Seq<i32>, x: i32)
        ensures
            Self::xor_fold(s.push(x)) == (Self::xor_fold(s) ^ x),
    {
        assert(s.push(x).drop_last() =~= s);
        assert(s.push(x).last() == x);
    }

    proof fn lemma_xor_fold_concat(a: Seq<i32>, b: Seq<i32>)
        ensures
            Self::xor_fold(a + b) == (Self::xor_fold(a) ^ Self::xor_fold(b)),
        decreases b.len(),
    {
        if b.len() == 0 {
            assert(a + b =~= a);
            assert(Self::xor_fold(b) == 0);
            assert(Self::xor_fold(a + b) == Self::xor_fold(a));
            let xa = Self::xor_fold(a);
            assert((xa ^ 0) == xa) by(bit_vector);
        } else {
            Self::lemma_xor_fold_concat(a, b.drop_last());
            assert((a + b.drop_last()).push(b.last()) =~= a + b);
            Self::lemma_xor_fold_push(a + b.drop_last(), b.last());
            Self::lemma_xor_fold_push(b.drop_last(), b.last());
            assert(Self::xor_fold(a + b.drop_last()) == (Self::xor_fold(a) ^ Self::xor_fold(b.drop_last())));
            assert(Self::xor_fold(a + b) == (Self::xor_fold(a + b.drop_last()) ^ b.last()));
            assert(Self::xor_fold(b) == (Self::xor_fold(b.drop_last()) ^ b.last()));
            let xa = Self::xor_fold(a);
            let y = Self::xor_fold(b.drop_last());
            let z = b.last();
            assert((xa ^ y) ^ z == (xa ^ (y ^ z))) by(bit_vector);
        }
    }

    proof fn lemma_xor_cancel(a: i32, b: i32)
        ensures
            ((a ^ b) ^ a) == b,
    {
        assert(((a ^ b) ^ a) == b) by(bit_vector);
    }

    pub fn xor_queries(arr: Vec<i32>, queries: Vec<Vec<i32>>) -> (answer: Vec<i32>)
        requires
            1 <= arr.len() <= 30_000,
            1 <= queries.len() <= 30_000,
            forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 1_000_000_000,
            forall |k: int|
                0 <= k < queries.len() ==> #[trigger] queries[k].len() == 2
                    && 0 <= queries[k][0] <= queries[k][1] < arr.len() as i32,
        ensures
            answer.len() == queries.len(),
            forall |k: int| 0 <= k < queries.len() ==> {
                queries[k].len() == 2
                && 0 <= queries[k][0] <= queries[k][1]
                && (queries[k][1] as int) < arr.len()
                && {
                let l = queries[k][0] as int;
                let r = queries[k][1] as int;
                #[trigger] answer[k] == Self::range_xor(arr@, l, r)
                }
            },
    {
        let n = arr.len();
        let mut pref: Vec<i32> = Vec::new();
        pref.push(0);

        let mut i: usize = 0;
        while i < n
            invariant
                n == arr.len(),
                pref.len() == i + 1,
                pref[0] == 0,
                0 <= i <= n,
                forall |k: int| 0 <= k < i ==> #[trigger] pref[k + 1] == (pref[k] ^ arr[k]),
                forall |k: int| 0 <= k <= i ==> #[trigger] pref[k] == Self::xor_fold(arr@.subrange(0, k)),
            decreases n - i,
        {
            let next = pref[i] ^ arr[i];
            pref.push(next);
            proof {
                assert(arr@.subrange(0, (i + 1) as int) =~= arr@.subrange(0, i as int).push(arr[i as int]));
                Self::lemma_xor_fold_push(arr@.subrange(0, i as int), arr[i as int]);
            }
            i += 1;
        }

        let mut answer: Vec<i32> = Vec::new();
        let mut q: usize = 0;
        while q < queries.len()
            invariant
                n == arr.len(),
                pref.len() == n + 1,
                pref[0] == 0,
                forall |k: int| 0 <= k < n ==> #[trigger] pref[k + 1] == (pref[k] ^ arr[k]),
                forall |k: int| 0 <= k <= n ==> #[trigger] pref[k] == Self::xor_fold(arr@.subrange(0, k)),
                0 <= q <= queries.len(),
                forall |k: int|
                    0 <= k < queries.len() ==> #[trigger] queries[k].len() == 2
                        && 0 <= queries[k][0] <= queries[k][1]
                        && (queries[k][1] as int) < n as int,
                answer.len() == q,
                forall |k: int| 0 <= k < q ==>
                    #[trigger] answer[k] == Self::range_xor(arr@, queries[k][0] as int, queries[k][1] as int),
            decreases queries.len() - q,
        {
            proof {
                assert(queries[q as int].len() == 2);
                assert(0 <= queries[q as int][0] <= queries[q as int][1]);
                assert((queries[q as int][1] as int) < n as int);
            }
            let l_i32 = queries[q][0];
            let r_i32 = queries[q][1];
            let l = l_i32 as usize;
            let r = r_i32 as usize;
            let v = pref[r + 1] ^ pref[l];
            proof {
                let li = l_i32 as int;
                let ri = r_i32 as int;
                assert(0 <= li <= ri < n as int);
                let a = arr@.subrange(0, li);
                let b = arr@.subrange(li, ri + 1);
                assert(arr@.subrange(0, ri + 1) =~= a + b);
                Self::lemma_xor_fold_concat(a, b);
                let xa = Self::xor_fold(a);
                let xb = Self::xor_fold(b);
                assert(pref[r as int + 1] == xa ^ xb);
                assert(pref[l as int] == xa);
                assert(v == (xa ^ xb) ^ xa);
                Self::lemma_xor_cancel(xa, xb);
                assert(v == xb);
                assert(xb == Self::range_xor(arr@, li, ri));
            }
            let ghost old_answer_view = answer@;
            answer.push(v);
            proof {
                assert(answer@ =~= old_answer_view.push(v));
                assert forall |k: int| 0 <= k < q as int implies
                    #[trigger] answer[k] == Self::range_xor(arr@, queries[k][0] as int, queries[k][1] as int)
                by {
                    assert(answer@[k] == old_answer_view[k]);
                };
                assert(answer[q as int] == v);
                assert(v == Self::range_xor(arr@, queries[q as int][0] as int, queries[q as int][1] as int));
            }
            q += 1;
        }

        answer
    }
}

}
