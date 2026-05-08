use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn start_teleports(c: Seq<i64>) -> int
        recommends
            c.len() >= 1,
    {
        c[0] as int - 1
    }

    pub open spec fn pos_step(c: Seq<i64>, i: int) -> int
        recommends
            c.len() >= 2,
            0 <= i < c.len() - 1,
    {
        let a = c[i + 1] as int;
        let b = c[i] as int;
        if a > b {
            a - b
        } else {
            0
        }
    }

    pub open spec fn spec_gap_sum(c: Seq<i64>, k: int) -> int
        recommends
            c.len() >= 1,
            0 <= k <= c.len() - 1,
            k > 0 ==> c.len() >= 2,
        decreases k,
    {
        if k <= 0 {
            0
        } else {
            Self::spec_gap_sum(c, k - 1) + Self::pos_step(c, k - 1)
        }
    }

    proof fn lemma_spec_gap_sum_unfold(c: Seq<i64>, k: int)
        requires
            c.len() >= 1,
            0 < k <= c.len() - 1,
        ensures
            Self::spec_gap_sum(c, k) == Self::spec_gap_sum(c, k - 1) + Self::pos_step(c, k - 1),
    {
    }

    proof fn lemma_pos_step_exec(c: Seq<i64>, j: int, ci: i64, cip1: i64)
        requires
            c.len() >= 2,
            0 <= j < c.len() - 1,
            ci == c[j],
            cip1 == c[j + 1],
            forall|x: int|
                0 <= x < c.len() ==> 0 <= #[trigger] c[x] as int <= 1_000_000_000,
        ensures
            Self::pos_step(c, j)
                == (if cip1 > ci {
                (cip1 as int) - (ci as int)
            } else {
                0int
            }),
    {
        assert(c[j] == ci);
        assert(c[j + 1] == cip1);
        assert(0 <= ci <= 1_000_000_000);
        assert(0 <= cip1 <= 1_000_000_000);
        let a = c[j + 1] as int;
        let b = c[j] as int;
        assert(a == cip1 as int);
        assert(b == ci as int);
        if cip1 > ci {
            assert(a > b);
            assert(Self::pos_step(c, j) == a - b);
            assert(a - b == (cip1 as int) - (ci as int));
        } else {
            assert(!(cip1 > ci));
            assert(!(a > b));
            assert(Self::pos_step(c, j) == 0);
        }
    }

    proof fn lemma_pos_step_bounded(c: Seq<i64>, j: int)
        requires
            c.len() >= 2,
            0 <= j < c.len() - 1,
            forall|x: int|
                0 <= x < c.len() ==> 0 <= #[trigger] c[x] as int <= 1_000_000_000,
        ensures
            0 <= Self::pos_step(c, j) <= 1_000_000_000,
    {
        let a = c[j + 1] as int;
        let b = c[j] as int;
        assert(0 <= a <= 1_000_000_000);
        assert(0 <= b <= 1_000_000_000);
        if a > b {
            assert(Self::pos_step(c, j) == a - b);
            assert(a - b <= a);
            assert(a <= 1_000_000_000);
            assert(0 <= a - b);
        } else {
            assert(Self::pos_step(c, j) == 0);
        }
    }

    proof fn lemma_gap_sum_bound(c: Seq<i64>, k: int)
        requires
            c.len() >= 1,
            0 <= k <= c.len() - 1,
            forall|x: int|
                0 <= x < c.len() ==> 0 <= #[trigger] c[x] as int <= 1_000_000_000,
        ensures
            Self::spec_gap_sum(c, k) <= k * 1_000_000_000,
        decreases k,
    {
        if k == 0 {
        } else {
            Self::lemma_gap_sum_bound(c, (k - 1) as int);
            Self::lemma_pos_step_bounded(c, (k - 1) as int);
            assert(0 < k <= c.len() - 1);
            assert(c.len() >= 2);
            assert(Self::spec_gap_sum(c, k) == Self::pos_step(c, k - 1) + Self::spec_gap_sum(c, k - 1));
            assert(Self::spec_gap_sum(c, k - 1) + Self::pos_step(c, k - 1) <= (k - 1) * 1_000_000_000 + 1_000_000_000);
            assert((k - 1) * 1_000_000_000 + 1_000_000_000 == k * 1_000_000_000);
        }
    }

    pub fn min_chip_teleports(c: Vec<i64>) -> (res: i64)
        requires
            1 <= c.len() <= 200_000,
            forall|i: int|
                0 <= i < c.len() as int ==> 0 <= #[trigger] c[i] as int <= 1_000_000_000,
            c[0] as int >= 1,
        ensures
            res as int == Self::start_teleports(c@) + Self::spec_gap_sum(c@, (c.len() as int) - 1),
            forall|i: int|
                0 <= i < c.len() as int - 1 ==> #[trigger] Self::pos_step(c@, i) >= 0,
    {
        let n = c.len();
        let mut ans: i64 = c[0] - 1;
        let mut j: usize = 0;
        proof {
            assert forall|i: int|
                0 <= i < c.len() as int - 1 implies Self::pos_step(c@, i) >= 0 by {
                if 0 <= i < c.len() as int - 1 {
                    Self::lemma_pos_step_bounded(c@, i);
                }
            };
        }
        let bound = n - 1;
        proof {
            assert((n as int) <= 200_000);
        }
        while j < bound
            invariant
                n == c.len(),
                (n as int) <= 200_000,
                bound == n - 1,
                forall|x: int|
                    0 <= x < c.len() as int ==> 0 <= #[trigger] c[x] as int <= 1_000_000_000,
                c[0] as int >= 1,
                j <= bound,
                (j as int) <= (c.len() as int) - 1,
                ans as int == Self::start_teleports(c@) + Self::spec_gap_sum(c@, j as int),
            decreases bound - j,
        {
            proof {
                assert(j < bound);
                assert(bound == n - 1);
                assert(n >= 2);
                assert((j as int) < (n as int) - 1);
                assert((j as int) < c.len() as int - 1);
                assert(0 <= (j as int) <= c.len() - 1);
                Self::lemma_gap_sum_bound(c@, j as int);
                assert(Self::spec_gap_sum(c@, j as int) <= (j as int) * 1_000_000_000);
                assert((j as int) <= 200_000);
                assert(Self::spec_gap_sum(c@, j as int) <= 200_000_000_000_000);
            }
            let ci = c[j];
            let cip1 = c[j + 1];
            let ghost jv = j as int;
            proof {
                assert(0 <= jv < c.len() as int - 1);
                assert(ci == c@[jv]);
                assert(cip1 == c@[jv + 1]);
                Self::lemma_pos_step_exec(c@, jv, ci, cip1);
            }
            let add: i64 = if cip1 > ci {
                cip1 - ci
            } else {
                0
            };
            proof {
                assert(add as int == Self::pos_step(c@, jv));
                assert(0 < (jv + 1) <= c.len() - 1);
                Self::lemma_spec_gap_sum_unfold(c@, jv + 1);
                assert(Self::spec_gap_sum(c@, jv + 1) == Self::spec_gap_sum(c@, jv) + Self::pos_step(c@, jv));
                Self::lemma_pos_step_bounded(c@, jv);
                assert(Self::spec_gap_sum(c@, jv) + Self::pos_step(c@, jv) <= jv * 1_000_000_000 + 1_000_000_000);
                assert(jv + 1 <= 200_000);
                assert(Self::spec_gap_sum(c@, jv) + Self::pos_step(c@, jv) <= 200_000 * 1_000_000_000);
                assert(200_000i64 * 1_000_000_000i64 <= 0x7fff_ffff_ffff_ffff);
                assert(ans as int + Self::pos_step(c@, jv) <= 200_000 * 1_000_000_000);
            }
            ans = ans + add;
            proof {
                assert(ans as int == Self::start_teleports(c@) + Self::spec_gap_sum(c@, jv + 1));
            }
            j = j + 1;
        }
        proof {
            assert(j <= bound);
            if n == 1 {
                assert(bound == 0);
                assert(!(j < bound));
                assert(j == 0);
                assert(ans as int == Self::start_teleports(c@) + Self::spec_gap_sum(c@, 0));
            } else {
                assert(n >= 2);
                assert(bound == n - 1);
                assert(!(j < bound));
                assert(j >= bound);
                assert(j <= bound);
                assert(j == bound);
                assert(j == n - 1);
                assert((j as int) == (n as int) - 1);
                assert(ans as int == Self::start_teleports(c@) + Self::spec_gap_sum(c@, (n as int) - 1));
            }
            assert(ans as int == Self::start_teleports(c@) + Self::spec_gap_sum(c@, (c.len() as int) - 1));
        }
        ans
    }
}

}
