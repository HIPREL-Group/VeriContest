use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn abs_diff(a: int, b: int) -> int {
        if a >= b { a - b } else { b - a }
    }

    pub open spec fn max2(a: int, b: int) -> int {
        if a >= b { a } else { b }
    }

    pub open spec fn one_change_cap(a: int, b: int, k: int) -> int {
        Self::max2(Self::max2(a, b), Self::max2(k - a, k - b))
    }

    pub open spec fn pair_cost(nums: Seq<i32>, k: int, i: int, d: int) -> int {
        let n = nums.len() as int;
        let a = nums[i] as int;
        let b = nums[n - 1 - i] as int;
        let cur_diff = if a >= b { a - b } else { b - a };
        let b1 = if k >= a { k - a } else { 0 };
        let b2 = if k >= b { k - b } else { 0 };
        let cap = Self::max2(Self::max2(a, b), Self::max2(b1, b2));
        if cur_diff == d {
            0
        } else if d <= cap {
            1
        } else {
            2
        }
    }

    pub open spec fn total_cost_from(nums: Seq<i32>, k: int, d: int, i: int) -> int
        decreases if i < nums.len() / 2 { nums.len() / 2 - i } else { 0 },
    {
        let pairs = nums.len() as int / 2;
        if i >= pairs {
            0
        } else {
            Self::pair_cost(nums, k, i, d) + Self::total_cost_from(nums, k, d, i + 1)
        }
    }

    pub open spec fn total_cost(nums: Seq<i32>, k: int, d: int) -> int {
        Self::total_cost_from(nums, k, d, 0)
    }

    pub open spec fn min_changes_spec(nums: Seq<i32>, k: i32, result: int) -> bool {
        &&& 2 <= nums.len() <= 100000
        &&& nums.len() % 2 == 0
        &&& 0 <= k <= 100000
        &&& forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= k
        &&& exists |d: int|
            0 <= d <= k as int
            && result == Self::total_cost(nums, k as int, d)
            && forall |d2: int| 0 <= d2 <= k as int ==> result <= Self::total_cost(nums, k as int, d2)
    }

    pub open spec fn total_cost_prefix(nums: Seq<i32>, k: int, d: int, ii: int) -> int
        decreases ii,
    {
        if ii <= 0 {
            0
        } else {
            Self::total_cost_prefix(nums, k, d, ii - 1) + Self::pair_cost(nums, k, ii - 1, d)
        }
    }

    proof fn lemma_total_prefix_suffix(nums: Seq<i32>, k: int, d: int, ii: int)
        requires
            0 <= ii <= nums.len() as int / 2,
        ensures
            Self::total_cost_prefix(nums, k, d, ii) + Self::total_cost_from(nums, k, d, ii)
                == Self::total_cost_from(nums, k, d, 0),
        decreases ii,
    {
        if ii > 0 {
            Self::lemma_total_prefix_suffix(nums, k, d, ii - 1);
        }
    }

    proof fn lemma_pair_cost_bounds(nums: Seq<i32>, k: int, i: int, d: int)
        ensures
            0 <= Self::pair_cost(nums, k, i, d) <= 2,
    {
    }

    proof fn lemma_total_cost_prefix_bounds(nums: Seq<i32>, k: int, d: int, ii: int)
        requires
            0 <= ii <= nums.len() as int / 2,
        ensures
            0 <= Self::total_cost_prefix(nums, k, d, ii) <= 2 * ii,
        decreases ii,
    {
        if ii > 0 {
            Self::lemma_total_cost_prefix_bounds(nums, k, d, ii - 1);
            Self::lemma_pair_cost_bounds(nums, k, ii - 1, d);
        }
    }

    proof fn lemma_pair_cost_zero_le_one(nums: Seq<i32>, k: int, i: int)
        ensures
            Self::pair_cost(nums, k, i, 0) <= 1,
    {
    }

    proof fn lemma_total_cost_prefix_zero_bound(nums: Seq<i32>, k: int, ii: int)
        requires
            0 <= ii <= nums.len() as int / 2,
        ensures
            0 <= Self::total_cost_prefix(nums, k, 0, ii) <= ii,
        decreases ii,
    {
        if ii > 0 {
            Self::lemma_total_cost_prefix_zero_bound(nums, k, ii - 1);
            Self::lemma_pair_cost_zero_le_one(nums, k, ii - 1);
        }
    }

    pub open spec fn spec_cc_prefix_sum(cc: Seq<i32>, d: int) -> int
        decreases d + 1,
    {
        if d < 0 {
            0
        } else {
            Self::spec_cc_prefix_sum(cc, d - 1) + cc[d] as int
        }
    }

    proof fn lemma_cc_prefix_sum_const(cc: Seq<i32>, val: int, d: int)
        requires
            0 <= d < cc.len(),
            cc[0] as int == val,
            forall|q: int| #![trigger cc[q]] 1 <= q < cc.len() ==> cc[q] == 0,
        ensures
            Self::spec_cc_prefix_sum(cc, d) == val,
        decreases d,
    {
        assert(Self::spec_cc_prefix_sum(cc, 0) == Self::spec_cc_prefix_sum(cc, -1) + cc[0] as int);
        assert(Self::spec_cc_prefix_sum(cc, -1) == 0);
        assert(Self::spec_cc_prefix_sum(cc, 0) == val);
        if d > 0 {
            Self::lemma_cc_prefix_sum_const(cc, val, d - 1);
            assert(cc[d] == 0);
            assert(Self::spec_cc_prefix_sum(cc, d) == Self::spec_cc_prefix_sum(cc, d - 1) + cc[d] as int);
        }
    }

    proof fn lemma_cc_prefix_sum_single_update(old_cc: Seq<i32>, new_cc: Seq<i32>, p: int, delta: int, d: int)
        requires
            0 <= p < old_cc.len(),
            new_cc.len() == old_cc.len(),
            0 <= d < old_cc.len(),
            forall|q: int| #![trigger new_cc[q]] 0 <= q < old_cc.len() && q != p ==> new_cc[q] == old_cc[q],
            new_cc[p] as int == old_cc[p] as int + delta,
        ensures
            Self::spec_cc_prefix_sum(new_cc, d) == Self::spec_cc_prefix_sum(old_cc, d)
                + (if p <= d { delta } else { 0 }),
        decreases d,
    {
        if d == p {
            assert(new_cc[d] as int == old_cc[d] as int + delta);
        } else {
            assert(new_cc[d] == old_cc[d]);
        }
        assert(Self::spec_cc_prefix_sum(new_cc, 0) == Self::spec_cc_prefix_sum(new_cc, -1) + new_cc[0] as int);
        assert(Self::spec_cc_prefix_sum(old_cc, 0) == Self::spec_cc_prefix_sum(old_cc, -1) + old_cc[0] as int);
        if d > 0 {
            Self::lemma_cc_prefix_sum_single_update(old_cc, new_cc, p, delta, d - 1);
            assert(Self::spec_cc_prefix_sum(new_cc, d) == Self::spec_cc_prefix_sum(new_cc, d - 1) + new_cc[d] as int);
            assert(Self::spec_cc_prefix_sum(old_cc, d) == Self::spec_cc_prefix_sum(old_cc, d - 1) + old_cc[d] as int);
        }
    }

    pub fn min_changes(nums: Vec<i32>, k: i32) -> (result: i32)
        requires
            2 <= nums.len() <= 100000,
            nums.len() % 2 == 0,
            0 <= k <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= k,
        ensures
            Self::min_changes_spec(nums@, k, result as int),
    {
        let n = nums.len();
        let pairs = n / 2;
        let ku = k as usize;
        let mut change_count = vec![0i32; ku + 2];
        change_count[0] = pairs as i32;

        proof {
            assert(change_count@[0] as int == pairs as int);
            assert forall|q: int| #![trigger change_count@[q]] 1 <= q < change_count.len() as int implies
                change_count@[q] == 0
            by {
                assert(change_count@[q] == 0);
            }
            assert forall|d: int| 0 <= d <= ku as int implies
                Self::spec_cc_prefix_sum(change_count@, d)
                    == pairs as int - 0 + Self::total_cost_prefix(nums@, k as int, d, 0)
            by {
                Self::lemma_cc_prefix_sum_const(change_count@, pairs as int, d);
            }
            assert forall|q: int| 0 <= q < change_count.len() as int implies
                -(3 * 0int) <= #[trigger] change_count[q] <= pairs as int + 3 * 0int
            by {
                if q == 0 {
                } else {
                    assert(change_count@[q] == 0);
                }
            }
        }

        let mut i = 0usize;
        while i < pairs
            invariant
                n == nums.len(),
                2 <= n <= 100000,
                n % 2 == 0,
                pairs == n / 2,
                pairs <= 50000,
                ku == k as usize,
                0 <= k <= 100000,
                0 <= i <= pairs,
                ku + 2 == change_count.len(),
                forall |j: int| 0 <= j < n as int ==> 0 <= #[trigger] nums[j] <= k,
                forall|d: int| 0 <= d <= ku as int ==>
                    Self::spec_cc_prefix_sum(change_count@, d)
                        == pairs as int - i as int + Self::total_cost_prefix(nums@, k as int, d, i as int),
                forall|q: int| 0 <= q < change_count.len() as int ==>
                    -(3 * i as int) <= #[trigger] change_count[q] <= pairs as int + 3 * i as int,
            decreases pairs - i,
        {
            let left = nums[i];
            let right = nums[n - 1 - i];
            let cur_diff_i32 = if left >= right {
                left.checked_sub(right).unwrap_or(0)
            } else {
                right.checked_sub(left).unwrap_or(0)
            };
            let cur_diff = cur_diff_i32 as usize;

            let a = if left >= right { left } else { right };
            let b1 = k.checked_sub(left).unwrap_or(0);
            let b2 = k.checked_sub(right).unwrap_or(0);
            let b = if b1 >= b2 { b1 } else { b2 };
            let max_diff_i32 = if a >= b { a } else { b };
            let max_diff = max_diff_i32 as usize;

            proof {
                let pi: int = i as int;
                assert(0 <= pi < n as int);
                assert(0 <= nums[pi] <= k);
                assert(0 <= nums[n as int - 1 - pi] <= k);
                assert(left as int == nums[pi]);
                assert(right as int == nums[n as int - 1 - pi]);
                assert(cur_diff_i32 as int == (if left as int >= right as int { left as int - right as int } else { right as int - left as int }));
                assert(b1 as int == (if k as int >= left as int { k as int - left as int } else { 0 }));
                assert(b2 as int == (if k as int >= right as int { k as int - right as int } else { 0 }));
                assert(max_diff_i32 as int == Self::max2(Self::max2(left as int, right as int), Self::max2(b1 as int, b2 as int)));
                assert(cur_diff as int == cur_diff_i32 as int);
                assert(max_diff as int == max_diff_i32 as int);
                assert(cur_diff as int <= k as int);
                assert(max_diff as int <= k as int);
                assert(cur_diff as int <= max_diff as int) by (nonlinear_arith)
                    requires
                        left as int >= 0, right as int >= 0,
                        cur_diff_i32 as int == (if left as int >= right as int { left as int - right as int } else { right as int - left as int }),
                        max_diff_i32 as int == Self::max2(Self::max2(left as int, right as int), Self::max2(b1 as int, b2 as int)),
                        cur_diff as int == cur_diff_i32 as int,
                        max_diff as int == max_diff_i32 as int,
                {
                }
            }

            let ghost cc0 = change_count@;
            let ghost budget = 3 * (i as int);

            proof {
                assert(-(budget) <= cc0[cur_diff as int] as int <= pairs as int + budget);
            }
            if cur_diff <= ku {
                let ghost prev = change_count@;
                change_count[cur_diff] = change_count[cur_diff].checked_sub(1).unwrap_or(change_count[cur_diff]);
                proof {
                    assert(change_count@[cur_diff as int] as int == prev[cur_diff as int] as int - 1);
                    assert forall|d: int| 0 <= d <= ku as int implies
                        Self::spec_cc_prefix_sum(change_count@, d)
                            == Self::spec_cc_prefix_sum(prev, d) + (if (cur_diff as int) <= d { -1int } else { 0int })
                    by {
                        Self::lemma_cc_prefix_sum_single_update(prev, change_count@, cur_diff as int, -1, d);
                    }
                }
                proof {
                    assert(change_count@[cur_diff as int + 1] as int == cc0[cur_diff as int + 1] as int);
                    assert(-(budget) <= cc0[cur_diff as int + 1] as int <= pairs as int + budget);
                }
                let ghost prev2 = change_count@;
                change_count[cur_diff + 1] = change_count[cur_diff + 1].checked_add(1).unwrap_or(change_count[cur_diff + 1]);
                proof {
                    assert(change_count@[cur_diff as int + 1] as int == prev2[cur_diff as int + 1] as int + 1);
                    assert forall|d: int| 0 <= d <= ku as int implies
                        Self::spec_cc_prefix_sum(change_count@, d)
                            == Self::spec_cc_prefix_sum(prev2, d) + (if (cur_diff as int + 1) <= d { 1int } else { 0int })
                    by {
                        Self::lemma_cc_prefix_sum_single_update(prev2, change_count@, cur_diff as int + 1, 1, d);
                    }
                }
            }
            proof {
                if max_diff as int + 1 == cur_diff as int + 1 {
                    assert(change_count@[max_diff as int + 1] as int == cc0[max_diff as int + 1] as int + 1);
                } else {
                    assert(change_count@[max_diff as int + 1] as int == cc0[max_diff as int + 1] as int);
                }
                assert(-(budget) <= cc0[max_diff as int + 1] as int <= pairs as int + budget);
                assert(-(budget) - 1 <= change_count@[max_diff as int + 1] as int <= pairs as int + budget + 1);
            }
            if max_diff <= ku {
                let ghost prev3 = change_count@;
                change_count[max_diff + 1] = change_count[max_diff + 1].checked_add(1).unwrap_or(change_count[max_diff + 1]);
                proof {
                    assert(change_count@[max_diff as int + 1] as int == prev3[max_diff as int + 1] as int + 1);
                    assert forall|d: int| 0 <= d <= ku as int implies
                        Self::spec_cc_prefix_sum(change_count@, d)
                            == Self::spec_cc_prefix_sum(prev3, d) + (if (max_diff as int + 1) <= d { 1int } else { 0int })
                    by {
                        Self::lemma_cc_prefix_sum_single_update(prev3, change_count@, max_diff as int + 1, 1, d);
                    }
                }
            }

            proof {
                assert forall|q: int| 0 <= q < change_count.len() as int implies
                    -(3 * (i as int + 1)) <= #[trigger] change_count[q] <= pairs as int + 3 * (i as int + 1)
                by {
                    if q == cur_diff as int || q == cur_diff as int + 1 || q == max_diff as int + 1 {
                        assert(-(budget) - 3 <= change_count[q] <= pairs as int + budget + 3);
                    } else {
                        assert(change_count@[q] == cc0[q]);
                        assert(-(budget) <= cc0[q] as int <= pairs as int + budget);
                    }
                }
            }

            proof {
                let pi: int = i as int;
                let cd: int = cur_diff as int;
                let md: int = max_diff as int;
                assert forall|d: int| 0 <= d <= ku as int implies
                    Self::spec_cc_prefix_sum(change_count@, d)
                        == pairs as int - (pi + 1) + Self::total_cost_prefix(nums@, k as int, d, pi + 1)
                by {
                    assert(Self::total_cost_prefix(nums@, k as int, d, pi + 1)
                        == Self::total_cost_prefix(nums@, k as int, d, pi) + Self::pair_cost(nums@, k as int, pi, d));
                    let base_delta: int = if (md + 1) <= d { 1int } else { 0int };
                    let disc_delta: int = (if cd <= d { -1int } else { 0int }) + (if cd + 1 <= d { 1int } else { 0int });
                    assert(Self::spec_cc_prefix_sum(change_count@, d) == Self::spec_cc_prefix_sum(cc0, d) + base_delta + disc_delta);
                    if d == cd {
                        assert(disc_delta == -1);
                        assert(Self::pair_cost(nums@, k as int, pi, d) == 0);
                    } else if d > cd {
                        assert(disc_delta == 0);
                        if d <= md {
                            assert(base_delta == 0);
                            assert(Self::pair_cost(nums@, k as int, pi, d) == 1);
                        } else {
                            assert(base_delta == 1);
                            assert(Self::pair_cost(nums@, k as int, pi, d) == 2);
                        }
                    } else {
                        assert(disc_delta == 0);
                        assert(base_delta == 0);
                        assert(d <= md);
                        assert(Self::pair_cost(nums@, k as int, pi, d) == 1);
                    }
                }
            }

            i += 1;
        }

        proof {
            assert forall|d: int| 0 <= d <= ku as int implies
                Self::spec_cc_prefix_sum(change_count@, d) == Self::total_cost(nums@, k as int, d)
            by {
                Self::lemma_total_prefix_suffix(nums@, k as int, d, pairs as int);
            }
            assert forall|d: int| 0 <= d <= ku as int implies
                0 <= #[trigger] Self::total_cost(nums@, k as int, d) <= 2 * pairs as int
            by {
                Self::lemma_total_cost_prefix_bounds(nums@, k as int, d, pairs as int);
                Self::lemma_total_prefix_suffix(nums@, k as int, d, pairs as int);
            }
        }

        let mut cur_changes = 0i32;
        let mut min_changes = pairs as i32;
        let mut d = 0usize;
        while d <= ku
            invariant
                ku + 2 == change_count.len(),
                ku == k as usize,
                0 <= k <= 100000,
                0 <= d <= ku + 1,
                n == nums.len(),
                pairs == n / 2,
                pairs <= 50000,
                forall |j: int| 0 <= j < n as int ==> 0 <= #[trigger] nums[j] <= k,
                forall|dv: int| 0 <= dv <= ku as int ==>
                    Self::spec_cc_prefix_sum(change_count@, dv) == Self::total_cost(nums@, k as int, dv),
                forall|dv: int| 0 <= dv <= ku as int ==>
                    0 <= #[trigger] Self::total_cost(nums@, k as int, dv) <= 2 * pairs as int,
                d == 0 ==> cur_changes as int == 0,
                d > 0 ==> cur_changes as int == Self::total_cost(nums@, k as int, d as int - 1),
                0 <= min_changes <= pairs as int,
                d == 0 ==> min_changes as int == pairs as int,
                d > 0 ==> exists|dv: int| 0 <= dv < d as int && min_changes as int == Self::total_cost(nums@, k as int, dv),
                forall|dv: int| 0 <= dv < d as int ==> min_changes as int <= Self::total_cost(nums@, k as int, dv),
            decreases ku + 1 - d,
        {
            proof {
                assert(0 <= d as int <= ku as int);
                assert(Self::spec_cc_prefix_sum(change_count@, d as int) == Self::total_cost(nums@, k as int, d as int));
                assert(0 <= Self::total_cost(nums@, k as int, d as int) <= 2 * pairs as int);
                assert(Self::spec_cc_prefix_sum(change_count@, d as int)
                    == Self::spec_cc_prefix_sum(change_count@, d as int - 1) + change_count[d as int] as int);
                if d > 0 {
                    assert(Self::spec_cc_prefix_sum(change_count@, d as int - 1)
                        == Self::total_cost(nums@, k as int, d as int - 1));
                    assert(0 <= Self::total_cost(nums@, k as int, d as int - 1) <= 2 * pairs as int);
                } else {
                    assert(Self::spec_cc_prefix_sum(change_count@, d as int - 1) == 0);
                }
                assert(-(2 * pairs as int) <= change_count[d as int] as int <= 2 * pairs as int);
            }
            cur_changes = cur_changes.checked_add(change_count[d]).unwrap_or(cur_changes);
            proof {
                assert(cur_changes as int == Self::total_cost(nums@, k as int, d as int));
            }
            let ghost old_min_changes = min_changes;
            if cur_changes < min_changes {
                min_changes = cur_changes;
            }
            proof {
                assert forall|dv: int| 0 <= dv < d as int + 1 implies
                    min_changes as int <= Self::total_cost(nums@, k as int, dv)
                by {
                    if dv < d as int {
                    } else {
                        assert(dv == d as int);
                    }
                };
                if cur_changes < old_min_changes {
                    assert(min_changes == cur_changes);
                    assert(min_changes as int == Self::total_cost(nums@, k as int, d as int));
                } else if d > 0 {
                    assert(min_changes == old_min_changes);
                    assert(exists|dv0: int| 0 <= dv0 < d as int && old_min_changes as int == Self::total_cost(nums@, k as int, dv0));
                    let dv0 = choose|dv0: int| 0 <= dv0 < d as int && old_min_changes as int == Self::total_cost(nums@, k as int, dv0);
                    assert(0 <= dv0 < d as int + 1 && min_changes as int == Self::total_cost(nums@, k as int, dv0));
                } else {
                    assert(d == 0);
                    assert(min_changes == old_min_changes);
                    assert(old_min_changes as int == pairs as int);
                    Self::lemma_total_cost_prefix_zero_bound(nums@, k as int, pairs as int);
                    Self::lemma_total_prefix_suffix(nums@, k as int, 0, pairs as int);
                    assert(Self::total_cost_prefix(nums@, k as int, 0, pairs as int)
                        + Self::total_cost_from(nums@, k as int, 0, pairs as int)
                        == Self::total_cost(nums@, k as int, 0));
                    assert(Self::total_cost_from(nums@, k as int, 0, pairs as int) == 0);
                    assert(Self::total_cost(nums@, k as int, 0) <= pairs as int);
                    assert(cur_changes as int == Self::total_cost(nums@, k as int, 0));
                    assert(cur_changes >= old_min_changes);
                    assert(min_changes as int == Self::total_cost(nums@, k as int, d as int));
                }
            }
            d += 1;
        }

        if min_changes < 0 { 0 } else { min_changes }
    }
}

}
