use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn max_d_for_index(i: int) -> int {
        i + 2
    }

    pub open spec fn good_at(a: Seq<i64>, i: int) -> bool
        recommends
            0 <= i < a.len(),
    {
        exists|d: int| 2 <= d <= Self::max_d_for_index(i) && #[trigger] ((a[i] as int) % d) != 0
    }

    pub open spec fn can_erase_spec(a: Seq<i64>) -> bool {
        forall|i: int| 0 <= i < a.len() ==> Self::good_at(a, i)
    }

    pub fn can_erase_all(a: Vec<i64>) -> (ok: bool)
        requires
            1 <= a.len() <= 100_000,
            forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 1_000_000_000,
        ensures
            ok == Self::can_erase_spec(a@),
    {
        let n = a.len();
        let mut i: usize = 0;

        while i < n
            invariant
                n == a.len(),
                1 <= n <= 100_000,
                0 <= i <= n,
                forall|j: int| 0 <= j < n ==> 1 <= #[trigger] a[j] <= 1_000_000_000,
                forall|j: int| 0 <= j < i ==> Self::good_at(a@, j),
            decreases
                n - i,
        {
            let mut ok = false;
            let mut d: i64 = 2;
            let lim: i64 = (i as i64) + 2;

            while d <= lim
                invariant
                    n == a.len(),
                    i < n,
                    2 <= d <= lim + 1,
                    lim == i as i64 + 2,
                    2 <= lim <= 100_002,
                    lim as int == Self::max_d_for_index(i as int),
                    forall|j: int| 0 <= j < n ==> 1 <= #[trigger] a[j] <= 1_000_000_000,
                    ok ==> exists|dd: int| 2 <= dd < d as int && dd <= lim as int && #[trigger] ((a[i as int] as int) % dd) != 0,
                    !ok ==> forall|dd: int| 2 <= dd < d as int && dd <= lim as int ==> #[trigger] ((a[i as int] as int) % dd) == 0,
                decreases
                    (lim + 1 - d) as int,
            {
                if a[i] % d != 0 {
                    ok = true;
                }
                d = d + 1;
            }

            proof {
                assert(lim as int == Self::max_d_for_index(i as int));
            }

            if !ok {
                proof {
                    assert forall|dd: int| 2 <= dd <= Self::max_d_for_index(i as int) implies #[trigger] ((a[i as int] as int) % dd) == 0 by {
                        assert(2 <= dd < d as int);
                    }
                    assert(!Self::good_at(a@, i as int));
                    assert(!Self::can_erase_spec(a@));
                }
                return false;
            }

            proof {
                let dd_w = choose|dd: int| 2 <= dd < d as int && dd <= lim as int && #[trigger] ((a[i as int] as int) % dd) != 0;
                assert(2 <= dd_w <= Self::max_d_for_index(i as int));
                assert((a[i as int] as int) % dd_w != 0);
                assert(Self::good_at(a@, i as int));
            }

            i = i + 1;
        }

        proof {
            assert(forall|j: int| 0 <= j < a@.len() ==> Self::good_at(a@, j));
            assert(Self::can_erase_spec(a@));
        }

        true
    }
}

}
