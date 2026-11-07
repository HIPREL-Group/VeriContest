use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn prefix_sum(differences: Seq<i32>, end: int) -> int
        recommends
            0 <= end <= differences.len(),
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::prefix_sum(differences, end - 1) + differences[end - 1] as int
        }
    }

    pub open spec fn min_prefix(differences: Seq<i32>, upto: int) -> int
        recommends
            0 <= upto <= differences.len(),
        decreases upto,
    {
        if upto <= 0 {
            0
        } else {
            let prev = Self::min_prefix(differences, upto - 1);
            let cur = Self::prefix_sum(differences, upto);
            if cur < prev {
                cur
            } else {
                prev
            }
        }
    }

    pub open spec fn max_prefix(differences: Seq<i32>, upto: int) -> int
        recommends
            0 <= upto <= differences.len(),
        decreases upto,
    {
        if upto <= 0 {
            0
        } else {
            let prev = Self::max_prefix(differences, upto - 1);
            let cur = Self::prefix_sum(differences, upto);
            if prev < cur {
                cur
            } else {
                prev
            }
        }
    }

    pub open spec fn number_of_arrays_spec(differences: Seq<i32>, lower: int, upper: int) -> int
        recommends
            lower <= upper,
    {
        let min_p = Self::min_prefix(differences, differences.len() as int);
        let max_p = Self::max_prefix(differences, differences.len() as int);
        let width = upper - lower;
        let span = max_p - min_p;
        if width < span {
            0
        } else {
            width - span + 1
        }
    }

    proof fn lemma_prefix_step(differences: Seq<i32>, i: int)
        requires
            0 <= i < differences.len(),
        ensures
            Self::prefix_sum(differences, i + 1) == Self::prefix_sum(differences, i) + differences[i] as int,
    {
    }

    proof fn lemma_min_prefix_step(differences: Seq<i32>, i: int)
        requires
            0 <= i < differences.len(),
        ensures
            Self::min_prefix(differences, i + 1)
                == if Self::prefix_sum(differences, i + 1) < Self::min_prefix(differences, i) {
                    Self::prefix_sum(differences, i + 1)
                } else {
                    Self::min_prefix(differences, i)
                },
    {
    }

    proof fn lemma_max_prefix_step(differences: Seq<i32>, i: int)
        requires
            0 <= i < differences.len(),
        ensures
            Self::max_prefix(differences, i + 1)
                == if Self::max_prefix(differences, i) < Self::prefix_sum(differences, i + 1) {
                    Self::prefix_sum(differences, i + 1)
                } else {
                    Self::max_prefix(differences, i)
                },
    {
    }

    pub fn number_of_arrays(differences: Vec<i32>, lower: i32, upper: i32) -> (result: i32)
        requires
            1 <= differences.len() <= 100_000,
            -100_000 <= lower <= upper <= 100_000,
            forall |i: int| 0 <= i < differences.len() ==> -100_000 <= #[trigger] differences[i] <= 100_000,
        ensures
            0 <= result,
            result as int == Self::number_of_arrays_spec(differences@, lower as int, upper as int),
    {
        let n = differences.len();
        let mut i: usize = 0;
        let mut cur: i128 = 0;
        let mut min_p: i128 = 0;
        let mut max_p: i128 = 0;

        while i < n
            invariant
                n == differences.len(),
                1 <= n <= 100_000,
                -100_000 <= lower <= upper <= 100_000,
                forall |k: int| 0 <= k < n ==> -100_000 <= #[trigger] differences[k] <= 100_000,
                0 <= i <= n,
                cur as int == Self::prefix_sum(differences@, i as int),
                min_p as int == Self::min_prefix(differences@, i as int),
                max_p as int == Self::max_prefix(differences@, i as int),
                min_p as int <= 0 <= max_p as int,
                -100_000 * (i as int) <= cur as int <= 100_000 * (i as int),
                -100_000 * (i as int) <= min_p as int <= 100_000 * (i as int),
                -100_000 * (i as int) <= max_p as int <= 100_000 * (i as int),
            decreases n - i,
        {
            let ghost old_i: int = i as int;
            let ghost old_cur: int = cur as int;
            let ghost old_min: int = min_p as int;
            let ghost old_max: int = max_p as int;

            proof {
                Self::lemma_prefix_step(differences@, old_i);
                Self::lemma_min_prefix_step(differences@, old_i);
                Self::lemma_max_prefix_step(differences@, old_i);
            }

            cur = cur + differences[i] as i128;
            proof {
                assert(cur as int == Self::prefix_sum(differences@, old_i + 1));
            }

            if cur < min_p {
                min_p = cur;
            }
            if max_p < cur {
                max_p = cur;
            }

            proof {
                if (cur as int) < old_min {
                    assert(min_p as int == cur as int);
                } else {
                    assert(min_p as int == old_min);
                }
                assert(min_p as int == (if (cur as int) < old_min { cur as int } else { old_min }));
                assert(min_p as int == Self::min_prefix(differences@, old_i + 1));
                assert(-100_000 * (old_i + 1) <= min_p as int <= 100_000 * (old_i + 1)) by (nonlinear_arith)
                    requires
                        -100_000 * old_i <= old_min <= 100_000 * old_i,
                        -100_000 * (old_i + 1) <= cur as int <= 100_000 * (old_i + 1),
                        min_p as int == (if (cur as int) < old_min { cur as int } else { old_min }),
                {
                }

                if old_max < (cur as int) {
                    assert(max_p as int == cur as int);
                } else {
                    assert(max_p as int == old_max);
                }
                assert(max_p as int == (if old_max < (cur as int) { cur as int } else { old_max }));
                assert(max_p as int == Self::max_prefix(differences@, old_i + 1));
                assert(-100_000 * (old_i + 1) <= max_p as int <= 100_000 * (old_i + 1)) by (nonlinear_arith)
                    requires
                        -100_000 * old_i <= old_max <= 100_000 * old_i,
                        -100_000 * (old_i + 1) <= cur as int <= 100_000 * (old_i + 1),
                        max_p as int == (if old_max < (cur as int) { cur as int } else { old_max }),
                {
                }

                assert(min_p as int <= 0) by {
                    assert(0 <= old_i + 1);
                    assert(0 <= differences@.len());
                    assert(Self::min_prefix(differences@, old_i + 1)
                        == if Self::prefix_sum(differences@, old_i + 1) < Self::min_prefix(differences@, old_i) {
                            Self::prefix_sum(differences@, old_i + 1)
                        } else {
                            Self::min_prefix(differences@, old_i)
                        });
                    assert(Self::min_prefix(differences@, old_i) <= 0);
                }

                assert(0 <= max_p as int) by {
                    assert(Self::max_prefix(differences@, old_i + 1)
                        == if Self::max_prefix(differences@, old_i) < Self::prefix_sum(differences@, old_i + 1) {
                            Self::prefix_sum(differences@, old_i + 1)
                        } else {
                            Self::max_prefix(differences@, old_i)
                        });
                    assert(0 <= Self::max_prefix(differences@, old_i));
                }

                assert(-100_000 * (old_i + 1) <= cur as int <= 100_000 * (old_i + 1));
            }

            i = i + 1;
        }

        let width: i128 = (upper as i128) - (lower as i128);
        proof {
            assert(-10_000_000_000 <= min_p as int <= 10_000_000_000) by (nonlinear_arith)
                requires
                    -100_000 * (n as int) <= min_p as int <= 100_000 * (n as int),
                    n <= 100_000,
            {
            }
            assert(-10_000_000_000 <= max_p as int <= 10_000_000_000) by (nonlinear_arith)
                requires
                    -100_000 * (n as int) <= max_p as int <= 100_000 * (n as int),
                    n <= 100_000,
            {
            }
        }
        let span: i128 = max_p - min_p;

        proof {
            assert(cur as int == Self::prefix_sum(differences@, n as int));
            assert(min_p as int == Self::min_prefix(differences@, n as int));
            assert(max_p as int == Self::max_prefix(differences@, n as int));
            assert(width as int == upper as int - lower as int);
            assert(span as int == Self::max_prefix(differences@, n as int) - Self::min_prefix(differences@, n as int));
            assert(0 <= span as int);
            assert(width as int <= 200_000);
        }

        if span > width {
            proof {
                assert((width as int) < (span as int));
                assert(Self::number_of_arrays_spec(differences@, lower as int, upper as int) == 0);
            }
            0
        } else {
            let ans: i128 = width - span + 1;
            proof {
                assert(0 <= ans as int);
                assert(ans as int <= 200_001);
                assert(ans <= i32::MAX as i128);
                assert(Self::number_of_arrays_spec(differences@, lower as int, upper as int)
                    == (upper as int - lower as int) - (Self::max_prefix(differences@, n as int) - Self::min_prefix(differences@, n as int)) + 1);
                assert(ans as int == Self::number_of_arrays_spec(differences@, lower as int, upper as int));
            }
            ans as i32
        }
    }
}

}
