use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_max(a: int, b: int) -> int {
        if a >= b { a } else { b }
    }

    pub open spec fn max_gap_after_removal_at_pos(a: Seq<i32>, k: int, pos: int) -> int
        recommends
            1 <= k < a.len() - 1,
            0 <= pos <= a.len() - 1,
        decreases a.len() - 1 - pos,
    {
        if pos >= a.len() - 1 {
            0
        } else if pos == k - 1 {
            let gap = a[k + 1] - a[k - 1];
            let rest = if k + 1 < a.len() - 1 {
                Self::max_gap_after_removal_at_pos(a, k, k + 1)
            } else {
                0
            };
            if gap > rest {
                gap
            } else {
                rest
            }
        } else {
            let gap = a[pos + 1] - a[pos];
            let rest = Self::max_gap_after_removal_at_pos(a, k, pos + 1);
            if gap > rest {
                gap
            } else {
                rest
            }
        }
    }

    pub open spec fn max_gap_after_removal(a: Seq<i32>, k: int) -> int
        recommends
            1 <= k < a.len() - 1,
    {
        Self::max_gap_after_removal_at_pos(a, k, 0)
    }

    pub open spec fn min_max_difficulty_spec(a: Seq<i32>, k: int) -> int
        recommends
            a.len() >= 3,
            1 <= k <= a.len() - 1,
        decreases a.len() - 1 - k,
    {
        if k >= a.len() - 1 {
            Self::max_gap_after_removal(a, a.len() - 2)
        } else {
            let current = Self::max_gap_after_removal(a, k);
            let rest = Self::min_max_difficulty_spec(a, k + 1);
            if current < rest {
                current
            } else {
                rest
            }
        }
    }

    proof fn lemma_spec_max_assoc(a: int, b: int, c: int)
        ensures
            Self::spec_max(a, Self::spec_max(b, c)) == Self::spec_max(Self::spec_max(a, b), c),
    {
    }

    proof fn lemma_max_gap_at_pos_nonneg(a: Seq<i32>, k: int, pos: int)
        requires
            1 <= k < a.len() - 1,
            0 <= pos,
            forall |i: int| 0 <= i < a.len() - 1 ==> #[trigger] a[i] < a[i + 1],
        ensures
            Self::max_gap_after_removal_at_pos(a, k, pos) >= 0,
        decreases a.len() - 1 - pos,
    {
        reveal_with_fuel(Solution::max_gap_after_removal_at_pos, 2);
        if pos >= a.len() - 1 {
        } else if pos == k - 1 {
            if k + 1 < a.len() - 1 {
                Self::lemma_max_gap_at_pos_nonneg(a, k, k + 1);
            }
        } else {
            Self::lemma_max_gap_at_pos_nonneg(a, k, pos + 1);
        }
    }

    proof fn lemma_unfold_at_k_minus_1(a: Seq<i32>, k: int)
        requires
            1 <= k < a.len() - 1,
        ensures
            Self::max_gap_after_removal_at_pos(a, k, k - 1) ==
                Self::spec_max(
                    (a[k + 1] - a[k - 1]) as int,
                    Self::max_gap_after_removal_at_pos(a, k, k + 1),
                ),
    {
        reveal_with_fuel(Solution::max_gap_after_removal_at_pos, 2);
    }

    proof fn lemma_min_max_ge(a: Seq<i32>, k: int, bound: int)
        requires
            a.len() >= 3,
            1 <= k < a.len() - 1,
            forall |j: int| k <= j < a.len() - 1 ==>
                #[trigger] Self::max_gap_after_removal(a, j) >= bound,
        ensures
            Self::min_max_difficulty_spec(a, k) >= bound,
        decreases a.len() - 1 - k,
    {
        reveal_with_fuel(Solution::min_max_difficulty_spec, 2);
        if k + 1 < a.len() - 1 {
            Self::lemma_min_max_ge(a, k + 1, bound);
        }
    }

    proof fn lemma_min_max_eq(a: Seq<i32>, min_val: int, k: int)
        requires
            a.len() >= 3,
            1 <= k < a.len() - 1,
            forall |j: int| k <= j < a.len() - 1 ==>
                #[trigger] Self::max_gap_after_removal(a, j) >= min_val,
            exists |j: int| k <= j < a.len() - 1 &&
                #[trigger] Self::max_gap_after_removal(a, j) == min_val,
        ensures
            Self::min_max_difficulty_spec(a, k) == min_val,
        decreases a.len() - 1 - k,
    {
        reveal_with_fuel(Solution::min_max_difficulty_spec, 2);
        if k + 1 >= a.len() - 1 {
            let witness = choose |j: int| k <= j < a.len() - 1 &&
                Self::max_gap_after_removal(a, j) == min_val;
            assert(witness == k);
        } else if Self::max_gap_after_removal(a, k) == min_val {
            Self::lemma_min_max_ge(a, k + 1, min_val);
        } else {
            let witness = choose |j: int| k <= j < a.len() - 1 &&
                Self::max_gap_after_removal(a, j) == min_val;
            assert(witness > k);
            Self::lemma_min_max_eq(a, min_val, k + 1);
        }
    }

    pub fn min_max_difficulty(a: Vec<i32>) -> (result: i32)
        requires
            a.len() >= 3,
            a.len() <= 100,
            forall |i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a@[i] <= 1000,
            forall |i: int| 0 <= i < a.len() - 1 ==> #[trigger] a@[i] < a@[i + 1],
        ensures
            forall |k: int| 1 <= k < a@.len() - 1 ==>
                #[trigger] Self::max_gap_after_removal(a@, k) >= result as int,
            exists |k: int| 1 <= k < a@.len() - 1 &&
                #[trigger] Self::max_gap_after_removal(a@, k) == result as int,
    {
        let n = a.len();
        let mut min_result = 10000;
        let mut k: usize = 1;
        while k < n - 1
            invariant
                n == a.len(),
                3 <= n <= 100,
                forall |i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a@[i] <= 1000,
                forall |i: int| 0 <= i < a.len() - 1 ==> #[trigger] a@[i] < a@[i + 1],
                1 <= k <= n - 1,
                0 <= min_result <= 10000,
                forall |j: int| 1 <= j < k as int ==>
                    #[trigger] Self::max_gap_after_removal(a@, j) >= min_result as int,
                k == 1 ==> min_result == 10000,
                k > 1 ==> (exists |j: int| 1 <= j < k as int &&
                    #[trigger] Self::max_gap_after_removal(a@, j) == min_result as int),
            decreases n - 1 - k,
        {
            let mut max_gap = 0;
            let mut i: usize = 0;
            proof {
                Self::lemma_max_gap_at_pos_nonneg(a@, k as int, 0);
            }
            while i < n - 1
                invariant
                    n == a.len(),
                    1 <= k < n - 1,
                    3 <= n <= 100,
                    forall |ii: int| 0 <= ii < a.len() ==> 1 <= #[trigger] a@[ii] <= 1000,
                    forall |ii: int| 0 <= ii < a.len() - 1 ==> #[trigger] a@[ii] < a@[ii + 1],
                    0 <= i <= n - 1,
                    0 <= max_gap <= 999,
                    i as int != k as int,
                    Self::max_gap_after_removal(a@, k as int) ==
                        Self::spec_max(max_gap as int,
                            Self::max_gap_after_removal_at_pos(a@, k as int, i as int)),
                decreases n - 1 - i,
            {
                proof {
                    reveal_with_fuel(Solution::max_gap_after_removal_at_pos, 2);
                }
                let gap = if i == k - 1 {
                    a[k + 1] - a[k - 1]
                } else {
                    a[i + 1] - a[i]
                };
                let old_max_gap = max_gap;
                if gap > max_gap {
                    max_gap = gap;
                }
                if i == k - 1 {
                    proof {
                        Self::lemma_unfold_at_k_minus_1(a@, k as int);
                        let rest = Self::max_gap_after_removal_at_pos(
                            a@, k as int, (k + 1) as int);
                        Self::lemma_spec_max_assoc(
                            old_max_gap as int, gap as int, rest);
                    }
                    i = k + 1;
                } else {
                    proof {
                        let rest = Self::max_gap_after_removal_at_pos(
                            a@, k as int, (i + 1) as int);
                        Self::lemma_spec_max_assoc(
                            old_max_gap as int, gap as int, rest);
                    }
                    i = i + 1;
                }
            }
            proof {
                reveal_with_fuel(Solution::max_gap_after_removal_at_pos, 1);
                assert(Self::max_gap_after_removal_at_pos(
                    a@, k as int, (n - 1) as int) == 0);
                assert(max_gap as int ==
                    Self::max_gap_after_removal(a@, k as int));
            }
            let old_min = min_result;
            if max_gap < min_result {
                min_result = max_gap;
            }
            proof {
                assert(max_gap as int ==
                    Self::max_gap_after_removal(a@, k as int));
                assert forall |j: int| 1 <= j < k as int + 1 implies
                    #[trigger] Self::max_gap_after_removal(a@, j)
                        >= min_result as int
                by {
                    if j == k as int {
                        assert(Self::max_gap_after_removal(a@, j)
                            == max_gap as int);
                    } else {
                        assert(Self::max_gap_after_removal(a@, j)
                            >= old_min as int);
                    }
                };
                if max_gap < old_min {
                    assert(min_result == max_gap);
                    assert(Self::max_gap_after_removal(a@, k as int)
                        == min_result as int);
                } else if k > 1 {
                    let w = choose |j: int| 1 <= j < k as int &&
                        #[trigger] Self::max_gap_after_removal(a@, j)
                            == old_min as int;
                    assert(Self::max_gap_after_removal(a@, w)
                        == min_result as int);
                }
            }
            k = k + 1;
        }
        proof {
            if n == 3 {
                assert(min_result as int ==
                    Self::max_gap_after_removal(a@, 1));
            } else {
                Self::lemma_min_max_eq(a@, min_result as int, 1);
            }
        }
        min_result
    }
}

}
