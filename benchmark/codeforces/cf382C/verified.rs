use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn sorted(nums: Seq<i64>) -> bool {
    forall|i: int| 0 <= i < nums.len() - 1 ==> #[trigger] nums[i] <= nums[i + 1]
}

pub open spec fn gap(nums: Seq<i64>, i: int) -> int
    recommends 0 <= i < nums.len() - 1,
{
    nums[i + 1] as int - nums[i] as int
}

pub open spec fn lifted_index(i: int, miss: int) -> int {
    if i < miss { i } else { i + 1 }
}

pub open spec fn fits_with_missing(nums: Seq<i64>, start: int, d: int, miss: int) -> bool {
    &&& d >= 0
    &&& 0 <= miss <= nums.len()
    &&& forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] as int == start + lifted_index(i, miss) * d
}

pub open spec fn is_candidate(nums: Seq<i64>, x: int) -> bool {
    exists|start: int, d: int, miss: int| {
        &&& fits_with_missing(nums, start, d, miss)
        &&& x == start + miss * d
    }
}

pub open spec fn min_gap(nums: Seq<i64>, end: int) -> int
    decreases end,
{
    if end <= 2 {
        gap(nums, 0)
    } else {
        let prev = min_gap(nums, end - 1);
        let cur = gap(nums, end - 2);
        if prev <= cur { prev } else { cur }
    }
}

pub open spec fn gap_pattern(nums: Seq<i64>, d: int, miss: int) -> bool {
    &&& nums.len() >= 1
    &&& d >= 0
    &&& 0 <= miss <= nums.len()
    &&& forall|i: int| 0 <= i < nums.len() - 1 ==> #[trigger] gap(nums, i) == if i + 1 == miss { 2 * d } else { d }
}

pub open spec fn candidate_start(nums: Seq<i64>, d: int, miss: int) -> int {
    if miss == 0 { nums[0] as int - d } else { nums[0] as int }
}

pub open spec fn candidate_value_from_pattern(nums: Seq<i64>, d: int, miss: int) -> int {
    candidate_start(nums, d, miss) + miss * d
}

proof fn lemma_fits_implies_gap_pattern(nums: Seq<i64>, start: int, d: int, miss: int, i: int)
    requires
        fits_with_missing(nums, start, d, miss),
        0 <= i < nums.len() - 1,
    ensures
        gap(nums, i) == if i + 1 == miss { 2 * d } else { d },
{
    assert(nums[i] as int == start + lifted_index(i, miss) * d);
    assert(nums[i + 1] as int == start + lifted_index(i + 1, miss) * d);
    if i + 1 == miss {
        assert(lifted_index(i, miss) == i);
        assert(lifted_index(i + 1, miss) == i + 2);
        assert(gap(nums, i) == (start + (i + 2) * d) - (start + i * d));
        assert((start + (i + 2) * d) - (start + i * d) == 2 * d) by (nonlinear_arith);
    } else {
        if i + 1 < miss {
            assert(lifted_index(i, miss) == i);
            assert(lifted_index(i + 1, miss) == i + 1);
            assert(gap(nums, i) == (start + (i + 1) * d) - (start + i * d));
            assert((start + (i + 1) * d) - (start + i * d) == d) by (nonlinear_arith);
        } else {
            assert(i + 1 > miss);
            assert(lifted_index(i, miss) == i + 1);
            assert(lifted_index(i + 1, miss) == i + 2);
            assert(gap(nums, i) == (start + (i + 2) * d) - (start + (i + 1) * d));
            assert((start + (i + 2) * d) - (start + (i + 1) * d) == d) by (nonlinear_arith);
        }
    }
}

proof fn lemma_min_gap_lower_bound(nums: Seq<i64>, end: int, i: int)
    requires
        2 <= end <= nums.len(),
        0 <= i < end - 1,
    ensures
        min_gap(nums, end) <= gap(nums, i),
    decreases end,
{
    if end == 2 {
    } else {
        let prev = min_gap(nums, end - 1);
        let cur = gap(nums, end - 2);
        if i < end - 2 {
            lemma_min_gap_lower_bound(nums, end - 1, i);
            if prev <= cur {
            } else {
                assert(min_gap(nums, end) == cur);
                assert(cur <= gap(nums, i));
            }
        } else {
            if prev <= cur {
                assert(min_gap(nums, end) == prev);
                assert(prev <= cur);
            } else {
                assert(min_gap(nums, end) == cur);
            }
        }
    }
}

proof fn lemma_min_gap_ge_if_all_ge(nums: Seq<i64>, end: int, d: int)
    requires
        2 <= end <= nums.len(),
        forall|i: int| 0 <= i < end - 1 ==> d <= #[trigger] gap(nums, i),
    ensures
        d <= min_gap(nums, end),
    decreases end,
{
    if end == 2 {
        assert(d <= gap(nums, 0));
    } else {
        lemma_min_gap_ge_if_all_ge(nums, end - 1, d);
        let prev = min_gap(nums, end - 1);
        let cur = gap(nums, end - 2);
        assert(d <= prev);
        assert(d <= cur);
        if prev <= cur {
            assert(min_gap(nums, end) == prev);
        } else {
            assert(min_gap(nums, end) == cur);
        }
    }
}

proof fn lemma_gap_pattern_has_plain_gap(nums: Seq<i64>, d: int, miss: int)
    requires
        gap_pattern(nums, d, miss),
        nums.len() >= 3,
    ensures
        exists|i: int| 0 <= i < nums.len() - 1 && gap(nums, i) == d,
{
    if miss != 1 {
        assert(0 <= 0 < nums.len() - 1);
        assert(gap(nums, 0) == d);
    } else {
        assert(nums.len() - 1 >= 2);
        assert(0 <= 1 < nums.len() - 1);
        assert(gap(nums, 1) == d);
    }
}

proof fn lemma_gap_pattern_implies_min_gap(nums: Seq<i64>, d: int, miss: int)
    requires
        gap_pattern(nums, d, miss),
        nums.len() >= 3,
    ensures
        min_gap(nums, nums.len() as int) == d,
{
    assert forall|i: int| 0 <= i < nums.len() - 1 implies d <= #[trigger] gap(nums, i) by {
        if i + 1 == miss {
            assert(gap(nums, i) == 2 * d);
            assert(d <= 2 * d) by (nonlinear_arith)
                requires d >= 0;
        } else {
            assert(gap(nums, i) == d);
        }
    }
    lemma_min_gap_ge_if_all_ge(nums, nums.len() as int, d);
    lemma_gap_pattern_has_plain_gap(nums, d, miss);
    let j = choose|i: int| 0 <= i < nums.len() - 1 && gap(nums, i) == d;
    lemma_min_gap_lower_bound(nums, nums.len() as int, j);
}

proof fn lemma_gap_pattern_formula(nums: Seq<i64>, d: int, miss: int, i: int)
    requires
        gap_pattern(nums, d, miss),
        0 <= i < nums.len(),
    ensures
        nums[i] as int == candidate_start(nums, d, miss) + lifted_index(i, miss) * d,
    decreases i,
{
    if i == 0 {
        if miss == 0 {
            assert(candidate_start(nums, d, miss) == nums[0] as int - d);
            assert(lifted_index(0, miss) == 1);
            assert(candidate_start(nums, d, miss) + lifted_index(0, miss) * d == (nums[0] as int - d) + d);
            assert((nums[0] as int - d) + d == nums[0] as int) by (nonlinear_arith);
        } else {
            assert(candidate_start(nums, d, miss) == nums[0] as int);
            assert(lifted_index(0, miss) == 0);
            assert(nums[0] as int == candidate_start(nums, d, miss) + lifted_index(0, miss) * d);
        }
    } else {
        lemma_gap_pattern_formula(nums, d, miss, i - 1);
        assert(gap(nums, i - 1) == if i == miss { 2 * d } else { d });
        if i == miss {
            assert(candidate_start(nums, d, miss) == nums[0] as int);
            assert(nums[i - 1] as int == candidate_start(nums, d, miss) + (i - 1) * d);
            assert(nums[i] as int == nums[i - 1] as int + 2 * d);
            assert(lifted_index(i, miss) == i + 1);
            assert(nums[i - 1] as int + 2 * d
                == (candidate_start(nums, d, miss) + (i - 1) * d) + 2 * d);
            assert(nums[i] as int == (candidate_start(nums, d, miss) + (i - 1) * d) + 2 * d);
            assert((candidate_start(nums, d, miss) + (i - 1) * d) + 2 * d
                == candidate_start(nums, d, miss) + (i + 1) * d) by (nonlinear_arith);
        } else {
            if miss == 0 {
                assert(candidate_start(nums, d, miss) == nums[0] as int - d);
            } else {
                assert(candidate_start(nums, d, miss) == nums[0] as int);
            }
            assert(nums[i] as int == nums[i - 1] as int + d);
            assert(lifted_index(i, miss) == lifted_index(i - 1, miss) + 1);
            assert(nums[i - 1] as int == candidate_start(nums, d, miss) + lifted_index(i - 1, miss) * d);
            assert(nums[i - 1] as int + d
                == (candidate_start(nums, d, miss) + lifted_index(i - 1, miss) * d) + d);
            assert(nums[i] as int == (candidate_start(nums, d, miss) + lifted_index(i - 1, miss) * d) + d);
            if i < miss {
                assert(lifted_index(i - 1, miss) == i - 1);
                assert(lifted_index(i, miss) == i);
                assert(lifted_index(i, miss) * d == i * d);
                assert((lifted_index(i - 1, miss) + 1) * d == i * d);
            } else {
                assert(i > miss);
                assert(lifted_index(i - 1, miss) == i);
                assert(lifted_index(i, miss) == i + 1);
                assert(lifted_index(i, miss) * d == (i + 1) * d);
                assert((lifted_index(i - 1, miss) + 1) * d == (i + 1) * d);
            }
            assert(candidate_start(nums, d, miss) + lifted_index(i, miss) * d
                == candidate_start(nums, d, miss) + (lifted_index(i - 1, miss) + 1) * d);
            assert(candidate_start(nums, d, miss) + (lifted_index(i - 1, miss) + 1) * d
                == (candidate_start(nums, d, miss) + lifted_index(i - 1, miss) * d) + d) by (nonlinear_arith);
        }
    }
}

proof fn lemma_gap_pattern_implies_candidate(nums: Seq<i64>, d: int, miss: int)
    requires
        gap_pattern(nums, d, miss),
    ensures
        is_candidate(nums, candidate_value_from_pattern(nums, d, miss)),
{
    assert(fits_with_missing(nums, candidate_start(nums, d, miss), d, miss)) by {
        assert forall|i: int| 0 <= i < nums.len() implies #[trigger] nums[i] as int
            == candidate_start(nums, d, miss) + lifted_index(i, miss) * d by {
            lemma_gap_pattern_formula(nums, d, miss, i);
        }
    }
}

proof fn lemma_candidate_matches_min_gap(nums: Seq<i64>, x: int)
    requires
        nums.len() >= 3,
        is_candidate(nums, x),
    ensures
        exists|miss: int| gap_pattern(nums, min_gap(nums, nums.len() as int), miss),
    {
        let witness = choose|start: int, d: int, miss: int| {
            &&& fits_with_missing(nums, start, d, miss)
            &&& x == start + miss * d
        };
        let start = witness.0;
        let d = witness.1;
        let miss = witness.2;
        assert(gap_pattern(nums, d, miss)) by {
            assert(nums.len() >= 1);
            assert(d >= 0);
            assert(0 <= miss <= nums.len());
            assert forall|i: int| 0 <= i < nums.len() - 1 implies #[trigger] gap(nums, i) == if i + 1 == miss { 2 * d } else { d } by {
                lemma_fits_implies_gap_pattern(nums, start, d, miss, i);
            }
        }
        lemma_gap_pattern_implies_min_gap(nums, d, miss);
        assert(gap_pattern(nums, min_gap(nums, nums.len() as int), miss));
    }
proof fn lemma_any_value_is_candidate_for_len_one(nums: Seq<i64>, x: int)
    requires
        nums.len() == 1,
    ensures
        is_candidate(nums, x),
{
    if x <= nums[0] as int {
        assert(fits_with_missing(nums, x, nums[0] as int - x, 0)) by {
            assert(nums[0] as int - x >= 0);
            assert(0 <= 0 <= nums.len());
            assert forall|i: int| 0 <= i < nums.len() implies #[trigger] nums[i] as int == x + lifted_index(i, 0) * (nums[0] as int - x) by {
                assert(i == 0);
                assert(lifted_index(i, 0) == 1);
            }
        }
        assert(x == x + 0 * (nums[0] as int - x));
    } else {
        assert(fits_with_missing(nums, nums[0] as int, x - nums[0] as int, 1)) by {
            assert(x - nums[0] as int >= 0);
            assert(0 <= 1 <= nums.len());
            assert forall|i: int| 0 <= i < nums.len() implies #[trigger] nums[i] as int
                == nums[0] as int + lifted_index(i, 1) * (x - nums[0] as int) by {
                assert(i == 0);
                assert(lifted_index(i, 1) == 0);
            }
        }
        assert(x == nums[0] as int + 1 * (x - nums[0] as int));
    }
}

proof fn lemma_two_element_candidates(nums: Seq<i64>, x: int)
    requires
        nums.len() == 2,
        sorted(nums),
        is_candidate(nums, x),
    ensures
        x == nums[0] as int - gap(nums, 0)
            || x == nums[1] as int + gap(nums, 0)
            || (gap(nums, 0) % 2 == 0 && x == nums[0] as int + gap(nums, 0) / 2),
{
    let witness = choose|start: int, d: int, miss: int| {
        &&& fits_with_missing(nums, start, d, miss)
        &&& x == start + miss * d
    };
    let start = witness.0;
    let d = witness.1;
    let miss = witness.2;
    assert(fits_with_missing(nums, start, d, miss));
    assert(x == start + miss * d);
    assert(0 <= miss <= 2);
    if miss == 0 {
        assert(nums[0] as int == start + lifted_index(0, miss) * d);
        assert(nums[1] as int == start + lifted_index(1, miss) * d);
        assert(lifted_index(0, miss) == 1);
        assert(lifted_index(1, miss) == 2);
        assert(start + lifted_index(0, miss) * d == start + 1 * d);
        assert(start + 1 * d == start + d) by (nonlinear_arith);
        assert(nums[0] as int == start + d);
        assert(nums[1] as int == start + 2 * d);
        assert(gap(nums, 0) == d);
        assert(x == start + 0 * d);
        assert(start + 0 * d == start) by (nonlinear_arith);
        assert(x == start);
    } else if miss == 1 {
        assert(nums[0] as int == start + lifted_index(0, miss) * d);
        assert(nums[1] as int == start + lifted_index(1, miss) * d);
        assert(lifted_index(0, miss) == 0);
        assert(lifted_index(1, miss) == 2);
        assert(start + lifted_index(0, miss) * d == start);
        assert(nums[0] as int == start);
        assert(nums[1] as int == start + 2 * d);
        assert(gap(nums, 0) == 2 * d);
        assert(gap(nums, 0) % 2 == 0);
        assert(x == start + 1 * d);
        assert(start + 1 * d == start + d) by (nonlinear_arith);
        assert(x == start + d);
        assert(x == nums[0] as int + gap(nums, 0) / 2);
    } else {
        assert(miss == 2);
        assert(nums[0] as int == start + lifted_index(0, miss) * d);
        assert(nums[1] as int == start + lifted_index(1, miss) * d);
        assert(lifted_index(0, miss) == 0);
        assert(lifted_index(1, miss) == 1);
        assert(nums[0] as int == start);
        assert(start + lifted_index(1, miss) * d == start + 1 * d);
        assert(start + 1 * d == start + d) by (nonlinear_arith);
        assert(nums[1] as int == start + d);
        assert(gap(nums, 0) == d);
        assert(x == start + miss * d);
        assert(x == start + 2 * d);
    }
}

impl Solution {
    pub fn arithmetic_progression_insertions(nums: Vec<i64>) -> (result: Option<Vec<i64>>)
        requires
            1 <= nums.len() <= 100_000,
            sorted(nums@),
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100_000_000,
        ensures
            result == None::<Vec<i64>> ==> nums.len() == 1 && forall|x: int| is_candidate(nums@, x),
            result != None::<Vec<i64>> ==> nums.len() >= 2,
            result != None::<Vec<i64>> ==> forall|i: int, j: int|
                0 <= i < j < result->0.len() ==> #[trigger] result->0[i] < #[trigger] result->0[j],
            result != None::<Vec<i64>> ==> forall|i: int|
                0 <= i < result->0.len() ==> is_candidate(nums@, #[trigger] result->0[i] as int),
            result != None::<Vec<i64>> ==> forall|x: int|
                is_candidate(nums@, x) ==> exists|i: int| 0 <= i < result->0.len() && result->0[i] as int == x,
    {
        let n = nums.len();
        if n == 1 {
            proof {
                assert forall|x: int| is_candidate(nums@, x) by {
                    lemma_any_value_is_candidate_for_len_one(nums@, x);
                }
            }
            return None;
        }

        if n == 2 {
            let a = nums[0];
            let b = nums[1];
            let d = b - a;
            if d == 0 {
                let mut ans = Vec::new();
                ans.push(a);
                proof {
                    assert(is_candidate(nums@, a as int)) by {
                        assert(gap_pattern(nums@, 0, 0));
                        lemma_gap_pattern_implies_candidate(nums@, 0, 0);
                        assert(candidate_value_from_pattern(nums@, 0, 0) == a as int);
                    }
                    assert forall|x: int| is_candidate(nums@, x) implies exists|i: int| 0 <= i < ans@.len() && ans@[i] as int == x by {
                        lemma_two_element_candidates(nums@, x);
                        assert(x == a as int);
                        assert(0 <= 0 < ans@.len());
                        assert(ans@[0] as int == x);
                    }
                    assert(forall|i: int, j: int| 0 <= i < j < ans@.len() ==> #[trigger] ans@[i] < #[trigger] ans@[j]);
                }
                let out = Some(ans);
                proof {
                    assert(out != None::<Vec<i64>>);
                    assert(out->0@.len() == 1);
                    assert(out->0@[0] == a);
                    assert forall|x: int| is_candidate(nums@, x) implies exists|i: int| 0 <= i < out->0@.len() && out->0@[i] as int == x by {
                        assert(x == a as int);
                        assert(0 <= 0 < out->0@.len());
                    }
                }
                return out;
            }
            if d % 2 == 0 {
                let mut ans = Vec::new();
                ans.push(a - d);
                ans.push(a + d / 2);
                ans.push(b + d);
                proof {
                    assert(gap_pattern(nums@, d as int, 0));
                    lemma_gap_pattern_implies_candidate(nums@, d as int, 0);
                    assert(candidate_value_from_pattern(nums@, d as int, 0) == (a - d) as int);
                    assert(gap_pattern(nums@, (d / 2) as int, 1));
                    lemma_gap_pattern_implies_candidate(nums@, (d / 2) as int, 1);
                    assert(candidate_value_from_pattern(nums@, (d / 2) as int, 1) == (a + d / 2) as int);
                    assert(gap_pattern(nums@, d as int, 2));
                    lemma_gap_pattern_implies_candidate(nums@, d as int, 2);
                    assert(candidate_value_from_pattern(nums@, d as int, 2) == (b + d) as int);
                    assert forall|x: int| is_candidate(nums@, x) implies exists|i: int| 0 <= i < ans@.len() && ans@[i] as int == x by {
                        lemma_two_element_candidates(nums@, x);
                        if x == (a - d) as int {
                            assert(0 <= 0 < ans@.len());
                            assert(ans@[0] as int == x);
                        } else if x == (a + d / 2) as int {
                            assert(0 <= 1 < ans@.len());
                            assert(ans@[1] as int == x);
                        } else {
                            assert(x == (b + d) as int);
                            assert(0 <= 2 < ans@.len());
                            assert(ans@[2] as int == x);
                        }
                    }
                }
                let out = Some(ans);
                proof {
                    assert(out != None::<Vec<i64>>);
                    assert(out->0@.len() == 3);
                    assert(out->0@[0] == a - d);
                    assert(out->0@[1] == a + d / 2);
                    assert(out->0@[2] == b + d);
                    assert forall|x: int| is_candidate(nums@, x) implies exists|i: int| 0 <= i < out->0@.len() && out->0@[i] as int == x by {
                        lemma_two_element_candidates(nums@, x);
                        if x == (a - d) as int {
                            assert(0 <= 0 < out->0@.len());
                        } else if x == (a + d / 2) as int {
                            assert(0 <= 1 < out->0@.len());
                        } else {
                            assert(x == (b + d) as int);
                            assert(0 <= 2 < out->0@.len());
                        }
                    }
                }
                return out;
            } else {
                let mut ans = Vec::new();
                ans.push(a - d);
                ans.push(b + d);
                proof {
                    assert(gap_pattern(nums@, d as int, 0));
                    lemma_gap_pattern_implies_candidate(nums@, d as int, 0);
                    assert(candidate_value_from_pattern(nums@, d as int, 0) == (a - d) as int);
                    assert(gap_pattern(nums@, d as int, 2));
                    lemma_gap_pattern_implies_candidate(nums@, d as int, 2);
                    assert(candidate_value_from_pattern(nums@, d as int, 2) == (b + d) as int);
                    assert forall|x: int| is_candidate(nums@, x) implies exists|i: int| 0 <= i < ans@.len() && ans@[i] as int == x by {
                        lemma_two_element_candidates(nums@, x);
                        if x == (a - d) as int {
                            assert(0 <= 0 < ans@.len());
                            assert(ans@[0] as int == x);
                        } else {
                            assert(x == (b + d) as int);
                            assert(0 <= 1 < ans@.len());
                            assert(ans@[1] as int == x);
                        }
                    }
                }
                let out = Some(ans);
                proof {
                    assert(out != None::<Vec<i64>>);
                    assert(out->0@.len() == 2);
                    assert(out->0@[0] == a - d);
                    assert(out->0@[1] == b + d);
                    assert forall|x: int| is_candidate(nums@, x) implies exists|i: int| 0 <= i < out->0@.len() && out->0@[i] as int == x by {
                        lemma_two_element_candidates(nums@, x);
                        if x == (a - d) as int {
                            assert(0 <= 0 < out->0@.len());
                        } else {
                            assert(x == (b + d) as int);
                            assert(0 <= 1 < out->0@.len());
                        }
                    }
                }
                return out;
            }
        }

        let mut min_diff = nums[1] - nums[0];
        let mut i = 1usize;
        while i + 1 < n
            invariant
                n == nums.len(),
                3 <= n <= 100_000,
                sorted(nums@),
                forall|k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100_000_000,
                1 <= i < n,
                0 <= min_diff as int <= 100_000_000,
                min_diff as int == min_gap(nums@, i as int + 1),
            decreases n - 1 - i,
        {
            let cur = nums[i + 1] - nums[i];
            if cur < min_diff {
                min_diff = cur;
            }
            proof {
                let prev = min_gap(nums@, i as int + 1);
                let next = min_gap(nums@, i as int + 2);
                assert(cur as int == gap(nums@, i as int));
                if prev <= cur as int {
                    assert(next == prev);
                } else {
                    assert(next == cur as int);
                }
            }
            i += 1;
        }

        let mut has_double = false;
        let mut double_idx = 0usize;
        let mut j = 0usize;
        while j + 1 < n
            invariant
                n == nums.len(),
                3 <= n <= 100_000,
                sorted(nums@),
                forall|k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100_000_000,
                min_diff as int == min_gap(nums@, n as int),
                0 <= min_diff as int <= 100_000_000,
                0 <= j < n,
                !has_double ==> forall|k: int| 0 <= k < j as int ==> #[trigger] gap(nums@, k) == min_diff as int,
                has_double ==> {
                    &&& 0 <= double_idx < j
                    &&& gap(nums@, double_idx as int) == 2 * (min_diff as int)
                    &&& forall|k: int| 0 <= k < j as int ==> (
                        #[trigger] gap(nums@, k) == min_diff as int
                        || (k == double_idx as int && gap(nums@, k) == 2 * (min_diff as int))
                    )
                },
            decreases n - 1 - j,
        {
            let cur = nums[j + 1] - nums[j];
            if cur == min_diff {
                j += 1;
                continue;
            }
            if cur == 2 * min_diff && !has_double {
                proof {
                    assert(2 * min_diff as int <= 200_000_000);
                    assert(200_000_000 < 9_223_372_036_854_775_807int);
                }
                has_double = true;
                double_idx = j;
                j += 1;
                continue;
            }
            let ans = Vec::new();
            proof {
                assert forall|x: int| is_candidate(nums@, x) implies false by {
                    lemma_candidate_matches_min_gap(nums@, x);
                    let miss = choose|m: int| gap_pattern(nums@, min_gap(nums@, nums.len() as int), m);
                    assert(cur as int == gap(nums@, j as int));
                    if cur as int != min_diff as int && cur as int != 2 * (min_diff as int) {
                        assert(gap(nums@, j as int) == if j as int + 1 == miss { 2 * (min_diff as int) } else { min_diff as int });
                        assert(false);
                    } else {
                        assert(cur == 2 * min_diff);
                        assert(has_double);
                        assert(gap(nums@, double_idx as int) == 2 * (min_diff as int));
                        assert(j as int != double_idx as int);
                        if double_idx as int + 1 == miss {
                            assert(gap(nums@, j as int) == min_diff as int);
                            assert(false);
                        } else {
                            assert(gap(nums@, double_idx as int) == min_diff as int);
                            assert(false);
                        }
                    }
                }
            }
            return Some(ans);
        }

        if min_diff == 0 {
            let mut ans = Vec::new();
            ans.push(nums[0]);
            proof {
                assert(gap_pattern(nums@, 0, 0));
                lemma_gap_pattern_implies_candidate(nums@, 0, 0);
                assert(candidate_value_from_pattern(nums@, 0, 0) == nums[0] as int);
                assert forall|x: int| is_candidate(nums@, x) implies exists|i: int| 0 <= i < ans@.len() && ans@[i] as int == x by {
                    lemma_candidate_matches_min_gap(nums@, x);
                    let miss = choose|m: int| gap_pattern(nums@, min_gap(nums@, nums.len() as int), m);
                    assert(min_gap(nums@, nums.len() as int) == 0);
                    let witness = choose|start: int, d: int, m: int| {
                        &&& fits_with_missing(nums@, start, d, m)
                        &&& x == start + m * d
                    };
                    assert(gap_pattern(nums@, witness.1, witness.2)) by {
                        assert(nums@.len() >= 1);
                        assert(witness.1 >= 0);
                        assert(0 <= witness.2 <= nums@.len());
                        assert forall|k: int| 0 <= k < nums@.len() - 1 implies #[trigger] gap(nums@, k) == if k + 1 == witness.2 { 2 * witness.1 } else { witness.1 } by {
                            lemma_fits_implies_gap_pattern(nums@, witness.0, witness.1, witness.2, k);
                        }
                    }
                    lemma_gap_pattern_implies_min_gap(nums@, witness.1, witness.2);
                    assert(witness.1 == 0);
                    assert(x == witness.0 + witness.2 * witness.1);
                    assert(x == witness.0);
                    assert(nums@[0] as int == witness.0 + lifted_index(0, witness.2) * 0);
                    assert(x == nums[0] as int);
                    assert(0 <= 0 < ans@.len());
                    assert(ans@[0] as int == x);
                }
            }
            let out = Some(ans);
            proof {
                assert(out != None::<Vec<i64>>);
                assert(out->0@ == ans@);
                assert forall|x: int| is_candidate(nums@, x) implies exists|i: int| 0 <= i < out->0@.len() && out->0@[i] as int == x by {
                    let i = choose|i: int| 0 <= i < ans@.len() && ans@[i] as int == x;
                    assert(0 <= i < out->0@.len());
                    assert(out->0@[i] == ans@[i]);
                }
            }
            return out;
        }

        if has_double {
            let mut ans = Vec::new();
            ans.push(nums[double_idx] + min_diff);
            proof {
                assert(gap_pattern(nums@, min_diff as int, double_idx as int + 1)) by {
                    assert(nums@.len() >= 1);
                    assert(min_diff as int >= 0);
                    assert(0 <= double_idx as int + 1 <= nums@.len());
                    assert forall|k: int| 0 <= k < nums@.len() - 1 implies #[trigger] gap(nums@, k) == if k + 1 == double_idx as int + 1 { 2 * (min_diff as int) } else { min_diff as int } by {
                        if k == double_idx as int {
                            assert(gap(nums@, k) == 2 * (min_diff as int));
                        } else {
                            assert(gap(nums@, k) == min_diff as int || k == double_idx as int);
                        }
                    }
                }
                lemma_gap_pattern_implies_candidate(nums@, min_diff as int, double_idx as int + 1);
                assert(candidate_start(nums@, min_diff as int, double_idx as int + 1) == nums@[0] as int);
                lemma_gap_pattern_formula(nums@, min_diff as int, double_idx as int + 1, double_idx as int);
                assert(nums@[double_idx as int] as int
                    == candidate_start(nums@, min_diff as int, double_idx as int + 1)
                        + double_idx as int * min_diff as int);
                assert(candidate_value_from_pattern(nums@, min_diff as int, double_idx as int + 1)
                    == candidate_start(nums@, min_diff as int, double_idx as int + 1)
                        + (double_idx as int + 1) * min_diff as int);
                assert(nums[double_idx as int] as int + min_diff as int
                    == (candidate_start(nums@, min_diff as int, double_idx as int + 1)
                        + double_idx as int * min_diff as int) + min_diff as int);
                assert(double_idx as int * min_diff as int + min_diff as int
                    == (double_idx as int + 1) * min_diff as int) by (nonlinear_arith);
                assert(candidate_value_from_pattern(nums@, min_diff as int, double_idx as int + 1)
                    == nums[double_idx as int] as int + min_diff as int);
                assert forall|x: int| is_candidate(nums@, x) implies exists|i: int| 0 <= i < ans@.len() && ans@[i] as int == x by {
                    let witness = choose|start: int, d: int, m: int| {
                        &&& fits_with_missing(nums@, start, d, m)
                        &&& x == start + m * d
                    };
                    assert(gap_pattern(nums@, witness.1, witness.2)) by {
                        assert(nums@.len() >= 1);
                        assert(witness.1 >= 0);
                        assert(0 <= witness.2 <= nums@.len());
                        assert forall|k: int| 0 <= k < nums@.len() - 1 implies #[trigger] gap(nums@, k) == if k + 1 == witness.2 { 2 * witness.1 } else { witness.1 } by {
                            lemma_fits_implies_gap_pattern(nums@, witness.0, witness.1, witness.2, k);
                        }
                    }
                    lemma_gap_pattern_implies_min_gap(nums@, witness.1, witness.2);
                    assert(witness.1 == min_diff as int);
                    if witness.2 != double_idx as int + 1 {
                        assert(gap(nums@, double_idx as int) == witness.1);
                        assert(gap(nums@, double_idx as int) == 2 * (min_diff as int));
                        assert(witness.1 == min_diff as int);
                        assert(false);
                    }
                    assert(nums@[double_idx as int] as int == witness.0 + double_idx as int * witness.1);
                    assert(x == witness.0 + (double_idx as int + 1) * witness.1);
                    assert(0 <= 0 < ans@.len());
                    assert(ans@[0] as int == x);
                }
            }
            let out = Some(ans);
            proof {
                assert(out != None::<Vec<i64>>);
                assert(out->0@ == ans@);
                assert forall|x: int| is_candidate(nums@, x) implies exists|i: int| 0 <= i < out->0@.len() && out->0@[i] as int == x by {
                    let i = choose|i: int| 0 <= i < ans@.len() && ans@[i] as int == x;
                    assert(0 <= i < out->0@.len());
                    assert(out->0@[i] == ans@[i]);
                }
            }
            return out;
        }

        let mut ans = Vec::new();
        ans.push(nums[0] - min_diff);
        ans.push(nums[n - 1] + min_diff);
        proof {
            assert(gap_pattern(nums@, min_diff as int, 0)) by {
                assert(nums@.len() >= 1);
                assert(min_diff as int >= 0);
                assert(0 <= 0 <= nums@.len());
                assert forall|k: int| 0 <= k < nums@.len() - 1 implies #[trigger] gap(nums@, k) == if k + 1 == 0 { 2 * (min_diff as int) } else { min_diff as int } by {
                    if has_double {
                        assert(false);
                    } else {
                        assert(gap(nums@, k) == min_diff as int);
                    }
                }
            }
            lemma_gap_pattern_implies_candidate(nums@, min_diff as int, 0);
            assert(candidate_value_from_pattern(nums@, min_diff as int, 0) == (nums[0] - min_diff) as int);
            assert(gap_pattern(nums@, min_diff as int, nums@.len() as int)) by {
                assert(nums@.len() >= 1);
                assert(min_diff as int >= 0);
                assert(0 <= nums@.len() <= nums@.len());
                assert forall|k: int| 0 <= k < nums@.len() - 1 implies #[trigger] gap(nums@, k) == if k + 1 == nums@.len() { 2 * (min_diff as int) } else { min_diff as int } by {
                    if has_double {
                        assert(false);
                    } else {
                        assert(gap(nums@, k) == min_diff as int);
                    }
                }
            }
            lemma_gap_pattern_implies_candidate(nums@, min_diff as int, nums@.len() as int);
            assert(candidate_start(nums@, min_diff as int, nums@.len() as int) == nums@[0] as int);
            lemma_gap_pattern_formula(nums@, min_diff as int, nums@.len() as int, nums@.len() as int - 1);
            assert(nums@[nums@.len() as int - 1] as int
                == candidate_start(nums@, min_diff as int, nums@.len() as int)
                    + (nums@.len() as int - 1) * min_diff as int);
            assert(candidate_value_from_pattern(nums@, min_diff as int, nums@.len() as int)
                == candidate_start(nums@, min_diff as int, nums@.len() as int)
                    + nums@.len() as int * min_diff as int);
            assert(nums[n as int - 1] as int + min_diff as int
                == (candidate_start(nums@, min_diff as int, nums@.len() as int)
                    + (nums@.len() as int - 1) * min_diff as int) + min_diff as int);
            assert(candidate_start(nums@, min_diff as int, nums@.len() as int)
                + ((nums@.len() as int - 1) * min_diff as int + min_diff as int)
                == candidate_start(nums@, min_diff as int, nums@.len() as int)
                    + nums@.len() as int * min_diff as int) by (nonlinear_arith);
            assert(candidate_value_from_pattern(nums@, min_diff as int, nums@.len() as int)
                == nums[n as int - 1] as int + min_diff as int);
            assert forall|x: int| is_candidate(nums@, x) implies exists|i: int| 0 <= i < ans@.len() && ans@[i] as int == x by {
                let witness = choose|start: int, d: int, m: int| {
                    &&& fits_with_missing(nums@, start, d, m)
                    &&& x == start + m * d
                };
                assert(gap_pattern(nums@, witness.1, witness.2)) by {
                    assert(nums@.len() >= 1);
                    assert(witness.1 >= 0);
                    assert(0 <= witness.2 <= nums@.len());
                    assert forall|k: int| 0 <= k < nums@.len() - 1 implies #[trigger] gap(nums@, k) == if k + 1 == witness.2 { 2 * witness.1 } else { witness.1 } by {
                        lemma_fits_implies_gap_pattern(nums@, witness.0, witness.1, witness.2, k);
                    }
                }
                lemma_gap_pattern_implies_min_gap(nums@, witness.1, witness.2);
                assert(witness.1 == min_diff as int);
                if 0 < witness.2 < nums@.len() {
                    assert(gap(nums@, witness.2 - 1) == 2 * witness.1);
                    assert(gap(nums@, witness.2 - 1) == 2 * (min_diff as int));
                    assert(!has_double);
                    assert(gap(nums@, witness.2 - 1) == min_diff as int);
                    assert(false);
                }
                if witness.2 == 0 {
                    assert(nums@[0] as int == witness.0 + lifted_index(0, witness.2) * witness.1);
                    assert(lifted_index(0, witness.2) == 1);
                    assert(nums@[0] as int == witness.0 + witness.1);
                    assert(x == witness.0);
                    assert(0 <= 0 < ans@.len());
                    assert(ans@[0] as int == x);
                } else {
                    assert(witness.2 == nums@.len());
                    assert(nums@[0] as int == witness.0);
                    assert(nums@[nums@.len() as int - 1] as int == witness.0 + (nums@.len() as int - 1) * witness.1);
                    assert(x == witness.0 + nums@.len() as int * witness.1);
                    assert(0 <= 1 < ans@.len());
                    assert(ans@[1] as int == x);
                }
            }
        }
        let out = Some(ans);
        proof {
            assert(out != None::<Vec<i64>>);
            assert(out->0@ == ans@);
            assert forall|x: int| is_candidate(nums@, x) implies exists|i: int| 0 <= i < out->0@.len() && out->0@[i] as int == x by {
                let i = choose|i: int| 0 <= i < ans@.len() && ans@[i] as int == x;
                assert(0 <= i < out->0@.len());
                assert(out->0@[i] == ans@[i]);
            }
        }
        out
    }
}

}
