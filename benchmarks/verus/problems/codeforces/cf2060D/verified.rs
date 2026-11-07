use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn remaining_val(a: Seq<i64>, i: int) -> int
        recommends
            0 <= i < a.len(),
        decreases i,
    {
        if i <= 0 {
            a[0] as int
        } else {
            let prev = Self::remaining_val(a, i - 1);
            if prev <= a[i] as int {
                a[i] as int - prev
            } else {
                0int
            }
        }
    }

    pub open spec fn is_sortable(a: Seq<i64>) -> bool {
        forall |i: int| 0 <= i < a.len() as int - 1 ==> Self::remaining_val(a, i) <= #[trigger] a[i + 1] as int
    }

    proof fn lemma_remaining_val_bounds(a: Seq<i64>, i: int)
        requires
            0 <= i < a.len(),
            forall |k: int| 0 <= k < a.len() ==> 0 <= #[trigger] a[k] <= 1_000_000_000,
        ensures
            0 <= Self::remaining_val(a, i) <= 1_000_000_000,
        decreases i,
    {
        if i == 0 {
        } else {
            Self::lemma_remaining_val_bounds(a, i - 1);
        }
    }

    pub fn can_sort(a: Vec<i64>) -> (result: bool)
        requires
            2 <= a.len() <= 200_000,
            forall |k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= 1_000_000_000,
        ensures
            result == Self::is_sortable(a@),
    {
        let n = a.len();
        let ghost orig = a@;
        let mut cur: i64 = a[0];
        let mut i: usize = 0;

        proof {
            assert(cur as int == Self::remaining_val(orig, 0));
            Self::lemma_remaining_val_bounds(orig, 0);
        }

        while i < n - 1
            invariant
                n == orig.len(),
                a.len() == n,
                a@ == orig,
                n >= 2,
                n <= 200_000,
                0 <= i <= n - 1,
                forall |k: int| 0 <= k < n ==> 1 <= #[trigger] orig[k] <= 1_000_000_000,
                cur as int == Self::remaining_val(orig, i as int),
                0 <= cur as int <= 1_000_000_000,
                forall |j: int| 0 <= j < i ==> Self::remaining_val(orig, j) <= #[trigger] orig[j + 1] as int,
            decreases n - 1 - i,
        {
            let next = a[i + 1];

            if cur > next {
                proof {
                    assert(Self::remaining_val(orig, i as int) > orig[i as int + 1] as int);
                    assert(!Self::is_sortable(orig));
                }
                return false;
            }

            let new_cur = next - cur;

            proof {
                assert(cur as int <= next as int);
                assert(Self::remaining_val(orig, i as int) <= orig[i as int + 1] as int);
                let rv = Self::remaining_val(orig, i as int);
                assert(rv <= orig[i as int + 1] as int);
                assert(Self::remaining_val(orig, i as int + 1) == orig[i as int + 1] as int - rv);
                assert(new_cur as int == next as int - cur as int);
                assert(new_cur as int == orig[i as int + 1] as int - Self::remaining_val(orig, i as int));
                assert(new_cur as int == Self::remaining_val(orig, i as int + 1));
                Self::lemma_remaining_val_bounds(orig, i as int + 1);
                assert forall |j: int| 0 <= j < i + 1 implies Self::remaining_val(orig, j) <= #[trigger] orig[j + 1] as int by {
                    if j < i as int {
                    } else {
                        assert(j == i as int);
                    }
                };
            }

            cur = new_cur;
            i = i + 1;
        }

        proof {
            assert(Self::is_sortable(orig));
        }
        true
    }
}

}
