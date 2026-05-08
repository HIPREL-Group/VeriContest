use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn x_at(x: Seq<i64>, j: int) -> int {
        x[j] as int
    }

    pub open spec fn middle_felled(x: Seq<i64>, h: Seq<i64>, i: int, last: int) -> int
        recommends
            x.len() == h.len(),
            1 <= x.len(),
            1 <= i < x.len(),
        decreases x.len() as int - i,
    {
        let n = x.len() as int;
        if i >= n - 1 {
            0
        } else if Self::x_at(x, i) > last + Self::x_at(h, i) {
            1 + Self::middle_felled(x, h, i + 1, Self::x_at(x, i))
        } else if Self::x_at(x, i) + Self::x_at(h, i) < Self::x_at(x, i + 1) {
            1 + Self::middle_felled(x, h, i + 1, Self::x_at(x, i) + Self::x_at(h, i))
        } else {
            Self::middle_felled(x, h, i + 1, Self::x_at(x, i))
        }
    }

    pub open spec fn woodcutters_answer(x: Seq<i64>, h: Seq<i64>) -> int {
        if x.len() <= 1 {
            x.len() as int
        } else {
            2 + Self::middle_felled(x, h, 1, Self::x_at(x, 0))
        }
    }

    proof fn lemma_middle_felled_base(x: Seq<i64>, h: Seq<i64>, i: int, last: int)
        requires
            x.len() == h.len(),
            1 <= x.len(),
            1 <= i < x.len() as int,
            i >= x.len() as int - 1,
        ensures
            Self::middle_felled(x, h, i, last) == 0,
    {
        reveal_with_fuel(Solution::middle_felled, 2);
    }

    proof fn lemma_middle_felled_nonneg(x: Seq<i64>, h: Seq<i64>, i: int, last: int)
        requires
            x.len() == h.len(),
            1 <= x.len(),
            1 <= i < x.len(),
        ensures
            Self::middle_felled(x, h, i, last) >= 0,
        decreases x.len() as int - i,
    {
        reveal_with_fuel(Solution::middle_felled, 2);
        let n = x.len() as int;
        if i >= n - 1 {
        } else if Self::x_at(x, i) > last + Self::x_at(h, i) {
            Self::lemma_middle_felled_nonneg(x, h, i + 1, Self::x_at(x, i));
        } else if Self::x_at(x, i) + Self::x_at(h, i) < Self::x_at(x, i + 1) {
            Self::lemma_middle_felled_nonneg(x, h, i + 1, Self::x_at(x, i) + Self::x_at(h, i));
        } else {
            Self::lemma_middle_felled_nonneg(x, h, i + 1, Self::x_at(x, i));
        }
    }

    proof fn lemma_mf_upper(x: Seq<i64>, h: Seq<i64>, i: int, last: int)
        requires
            x.len() == h.len(),
            2 <= x.len(),
            1 <= i < x.len() as int,
            forall |j: int| 0 <= j < x.len() - 1 ==> x[j] < #[trigger] x[j + 1],
        ensures
            Self::middle_felled(x, h, i, last) <= x.len() as int - 1 - i,
        decreases x.len() as int - i,
    {
        reveal_with_fuel(Solution::middle_felled, 2);
        let n = x.len() as int;
        if i >= n - 1 {
            assert(Self::middle_felled(x, h, i, last) == 0);
            assert(x.len() as int - 1 - i == 0);
        } else if Self::x_at(x, i) > last + Self::x_at(h, i) {
            Self::lemma_mf_upper(x, h, i + 1, Self::x_at(x, i));
            assert((x.len() as int - 1 - (i + 1)) == (x.len() as int - 1 - i) - 1);
        } else if Self::x_at(x, i) + Self::x_at(h, i) < Self::x_at(x, i + 1) {
            Self::lemma_mf_upper(x, h, i + 1, Self::x_at(x, i) + Self::x_at(h, i));
            assert((x.len() as int - 1 - (i + 1)) == (x.len() as int - 1 - i) - 1);
        } else {
            Self::lemma_mf_upper(x, h, i + 1, Self::x_at(x, i));
            assert((x.len() as int - 1 - (i + 1)) == (x.len() as int - 1 - i) - 1);
        }
    }

    proof fn lemma_wa_le_len(x: Seq<i64>, h: Seq<i64>)
        requires
            x.len() == h.len(),
            1 <= x.len(),
            forall |j: int| 0 <= j < x.len() - 1 ==> x[j] < #[trigger] x[j + 1],
        ensures
            Self::woodcutters_answer(x, h) <= x.len() as int,
    {
        if x.len() <= 1 {
        } else {
            Self::lemma_mf_upper(x, h, 1, Self::x_at(x, 0));
            assert(Self::woodcutters_answer(x, h) == 2 + Self::middle_felled(x, h, 1, Self::x_at(x, 0)));
            assert(Self::middle_felled(x, h, 1, Self::x_at(x, 0)) <= x.len() as int - 2);
            assert(2 + (x.len() as int - 2) == x.len() as int);
        }
    }

    proof fn lemma_middle_felled_step(
        x: Seq<i64>,
        h: Seq<i64>,
        i: int,
        last: int,
    )
        requires
            x.len() == h.len(),
            2 <= x.len(),
            1 <= i && i + 1 < x.len() as int,
            forall |j: int| 0 <= j < x.len() - 1 ==> x[j] < #[trigger] x[j + 1],
        ensures
            Self::middle_felled(x, h, i, last) == if Self::x_at(x, i) > last + Self::x_at(h, i) {
                1 + Self::middle_felled(x, h, i + 1, Self::x_at(x, i))
            } else if Self::x_at(x, i) + Self::x_at(h, i) < Self::x_at(x, i + 1) {
                1 + Self::middle_felled(x, h, i + 1, Self::x_at(x, i) + Self::x_at(h, i))
            } else {
                Self::middle_felled(x, h, i + 1, Self::x_at(x, i))
            },
    {
        reveal_with_fuel(Solution::middle_felled, 2);
    }

    pub fn max_felled_trees(x: Vec<i64>, h: Vec<i64>) -> (result: i64)
        requires
            x.len() == h.len(),
            1 <= x.len() <= 100_000,
            forall |j: int| 0 <= j < x.len() ==> 1 <= #[trigger] x@[j] <= 1_000_000_000,
            forall |j: int| 0 <= j < h.len() ==> 1 <= #[trigger] h@[j] <= 1_000_000_000,
            forall |j: int| 0 <= j < x.len() - 1 ==> x@[j] < #[trigger] x@[j + 1],
        ensures
            result as int == Self::woodcutters_answer(x@, h@),
    {
        let n = x.len();
        if n == 1 {
            assert(Self::woodcutters_answer(x@, h@) == 1);
            return 1i64;
        }
        let mut ans: i64 = 2;
        let mut last: i64 = x[0];
        let mut i: usize = 1;
        assert(2 <= n);
        assert(Self::woodcutters_answer(x@, h@) == 2 + Self::middle_felled(x@, h@, 1, Self::x_at(x@, 0)));
        while i < n - 1
            invariant
                x.len() == n,
                h.len() == n,
                2 <= n && n <= 100_000,
                1 <= i && i <= n - 1,
                1 <= (last as int) && (last as int) <= 2_000_000_000,
                forall |j: int| 0 <= j < x.len() ==> 1 <= #[trigger] x@[j] <= 1_000_000_000,
                forall |j: int| 0 <= j < h.len() ==> 1 <= #[trigger] h@[j] <= 1_000_000_000,
                forall |j: int| 0 <= j < x.len() - 1 ==> x@[j] < #[trigger] x@[j + 1],
                (ans as int) <= (n as int),
                ans as int + Self::middle_felled(x@, h@, i as int, last as int)
                    == 2 + Self::middle_felled(x@, h@, 1, Self::x_at(x@, 0)),
            decreases n - 1 - i,
        {
            let xi = x[i];
            let hi = h[i];
            proof {
                assert(1 <= i as int);
                assert(i as int + 1 < x.len() as int);
                assert(x@[i as int] == xi);
                assert(h@[i as int] == hi);
                assert(1 <= #[trigger] x@[i as int] && #[trigger] x@[i as int] <= 1_000_000_000);
                assert(1 <= #[trigger] h@[i as int] && #[trigger] h@[i as int] <= 1_000_000_000);
                assert((last as int) + (hi as int) <= 3_000_000_000);
                assert((xi as int) + (hi as int) <= 2_000_000_000);
            }
            proof {
                Self::lemma_middle_felled_step(x@, h@, i as int, last as int);
            }
            if xi > last + hi {
                proof {
                    assert((last as int) + (hi as int) == (last + hi) as int);
                    assert((xi as int) > (last as int) + (hi as int));
                    assert(Self::x_at(x@, i as int) == (xi as int));
                    assert(Self::x_at(h@, i as int) == (hi as int));
                    assert(Self::x_at(x@, i as int) > (last as int) + Self::x_at(h@, i as int));
                    assert(Self::middle_felled(x@, h@, i as int, last as int) == 1 + Self::middle_felled(x@, h@, i as int + 1, xi as int));
                }
                assert((ans + 1) as int + Self::middle_felled(x@, h@, i as int + 1, xi as int)
                    == ans as int + Self::middle_felled(x@, h@, i as int, last as int));
                ans = ans + 1;
                last = xi;
            } else if xi + hi < x[i + 1] {
                proof {
                    assert(!(xi > last + hi));
                    assert((xi as int) + (hi as int) == (xi + hi) as int);
                    assert(Self::x_at(x@, i as int + 1) == (x[i + 1] as int));
                    assert(!(Self::x_at(x@, i as int) > (last as int) + Self::x_at(h@, i as int)));
                    assert(Self::x_at(x@, i as int) + Self::x_at(h@, i as int) < Self::x_at(x@, i as int + 1));
                    assert(Self::middle_felled(x@, h@, i as int, last as int) == 1 + Self::middle_felled(x@, h@, i as int + 1, Self::x_at(x@, i as int) + Self::x_at(h@, i as int)));
                }
                assert((ans + 1) as int + Self::middle_felled(x@, h@, i as int + 1, Self::x_at(x@, i as int) + Self::x_at(h@, i as int))
                    == ans as int + Self::middle_felled(x@, h@, i as int, last as int));
                ans = ans + 1;
                last = xi + hi;
            } else {
                proof {
                    assert(!(xi > last + hi));
                    assert(!(xi + hi < x[i + 1]));
                    assert(!(Self::x_at(x@, i as int) > (last as int) + Self::x_at(h@, i as int)));
                    assert(!(Self::x_at(x@, i as int) + Self::x_at(h@, i as int) < Self::x_at(x@, i as int + 1)));
                    assert(Self::middle_felled(x@, h@, i as int, last as int) == Self::middle_felled(x@, h@, i as int + 1, xi as int));
                }
                assert(ans as int + Self::middle_felled(x@, h@, i as int + 1, xi as int)
                    == ans as int + Self::middle_felled(x@, h@, i as int, last as int));
                last = xi;
            }
            i = i + 1;
            proof {
                assert(i as int <= n as int - 1);
                assert((ans as int) + Self::middle_felled(x@, h@, i as int, last as int) == Self::woodcutters_answer(x@, h@));
                Self::lemma_middle_felled_nonneg(x@, h@, i as int, last as int);
                Self::lemma_wa_le_len(x@, h@);
                assert((ans as int) <= Self::woodcutters_answer(x@, h@));
                assert(Self::woodcutters_answer(x@, h@) <= (n as int));
                assert((ans as int) <= (n as int));
            }
        }
        proof {
            assert(!(i < n - 1));
            assert(i >= n - 1);
            assert(i as int >= n as int - 1);
            Self::lemma_middle_felled_base(x@, h@, i as int, last as int);
            assert(Self::middle_felled(x@, h@, i as int, last as int) == 0);
            assert(ans as int == 2 + Self::middle_felled(x@, h@, 1, Self::x_at(x@, 0)));
            assert(ans as int == Self::woodcutters_answer(x@, h@));
        }
        ans
    }
}

}
