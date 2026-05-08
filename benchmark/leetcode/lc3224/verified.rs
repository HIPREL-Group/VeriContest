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
        change_count.set(0, pairs as i32);

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

            if cur_diff <= ku {
                change_count.set(cur_diff, change_count[cur_diff].checked_sub(1).unwrap_or(change_count[cur_diff]));
                change_count.set(cur_diff + 1, change_count[cur_diff + 1].checked_add(1).unwrap_or(change_count[cur_diff + 1]));
            }
            if max_diff <= ku {
                change_count.set(max_diff + 1, change_count[max_diff + 1].checked_add(1).unwrap_or(change_count[max_diff + 1]));
            }

            i += 1;
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
                forall |j: int| 0 <= j < n as int ==> 0 <= #[trigger] nums[j] <= k,
            decreases ku + 1 - d,
        {
            cur_changes = cur_changes.checked_add(change_count[d]).unwrap_or(cur_changes);
            if cur_changes < min_changes {
                min_changes = cur_changes;
            }
            d += 1;
        }

        let mut best = pairs as i32;
        let mut best_d = 0i32;
        let mut dd = 0i32;
        while dd <= k
            invariant
                n == nums.len(),
                pairs == n / 2,
                pairs <= 50000,
                0 <= k <= 100000,
                0 <= dd <= k + 1,
                0 <= best <= 2 * pairs as int,
                forall |j: int| 0 <= j < n as int ==> 0 <= #[trigger] nums[j] <= k,
                dd == 0 ==> best == pairs as int,
                dd > 0 ==> (0 <= best_d < dd && best == Self::total_cost(nums@, k as int, best_d as int)),
                forall |d2: int| 0 <= d2 < dd ==> best <= Self::total_cost(nums@, k as int, d2),
            decreases (k - dd + 1) as int,
        {
            let mut cost = 0i32;
            let mut p = 0usize;
            while p < pairs
                invariant
                    n == nums.len(),
                    pairs == n / 2,
                    pairs <= 50000,
                    0 <= p <= pairs,
                    0 <= cost <= 2 * p as int,
                    0 <= dd <= k,
                    0 <= k <= 100000,
                    forall |j: int| 0 <= j < n as int ==> 0 <= #[trigger] nums[j] <= k,
                    cost as int + Self::total_cost_from(nums@, k as int, dd as int, p as int) == Self::total_cost(nums@, k as int, dd as int),
                decreases pairs - p,
            {
                assert(p < pairs);
                let left = nums[p];
                let right = nums[n - 1 - p];
                proof {
                    let pi: int = p as int;
                    let qi: int = (n - 1 - p) as int;
                    assert(0 <= pi < nums.len());
                    assert(0 <= qi < nums.len());
                    assert(0 <= nums[pi] <= k);
                    assert(0 <= nums[qi] <= k);
                    assert(left == nums[pi]);
                    assert(right == nums[qi]);
                    assert(0 <= left <= k);
                    assert(0 <= right <= k);
                }
                let cur_diff_i32 = if left >= right {
                    left - right
                } else {
                    right - left
                };

                let a = if left >= right { left } else { right };
                let b1 = if k >= left { k - left } else { 0 };
                let b2 = if k >= right { k - right } else { 0 };
                let b = if b1 >= b2 { b1 } else { b2 };
                let max_diff_i32 = if a >= b { a } else { b };

                let add = if cur_diff_i32 == dd {
                    0i32
                } else if dd <= max_diff_i32 {
                    1i32
                } else {
                    2i32
                };

                proof {
                    let pi: int = p as int;
                    let dn: int = dd as int;
                    assert(0 <= pi < pairs as int);
                    assert(nums@[pi] == left);
                    assert(nums@[n as int - 1 - pi] == right);
                    assert(cur_diff_i32 as int == (if left as int >= right as int { left as int - right as int } else { right as int - left as int }));
                    assert(b1 as int == (if k as int >= left as int { k as int - left as int } else { 0 }));
                    assert(b2 as int == (if k as int >= right as int { k as int - right as int } else { 0 }));
                    assert(max_diff_i32 as int == Self::max2(Self::max2(left as int, right as int), Self::max2(b1 as int, b2 as int)));
                    assert((cur_diff_i32 == dd) <==> (cur_diff_i32 as int == dn));
                    assert((dd <= max_diff_i32) <==> (dn <= max_diff_i32 as int));
                    assert(Self::pair_cost(nums@, k as int, pi, dn)
                        == if cur_diff_i32 as int == dn {
                            0int
                        } else if dn <= max_diff_i32 as int {
                            1int
                        } else {
                            2int
                        });
                    assert(add as int == Self::pair_cost(nums@, k as int, pi, dn));
                    assert(Self::total_cost_from(nums@, k as int, dn, pi)
                        == Self::pair_cost(nums@, k as int, pi, dn)
                         + Self::total_cost_from(nums@, k as int, dn, pi + 1));
                }

                assert(0 <= add <= 2);
                assert(cost + add <= 2 * p as int + 2);
                assert(p < pairs);
                assert((p + 1) as int <= pairs as int);
                assert(2 * p as int + 2 == 2 * (p as int + 1));
                assert(2 * (p as int + 1) <= 2 * pairs as int);
                assert(2 * pairs as int <= 100000);
                assert(cost + add <= 100000);
                assert(cost + add <= 2147483647);

                cost = cost + add;
                p += 1;
            }

            proof {
                assert(Self::total_cost_from(nums@, k as int, dd as int, pairs as int) == 0);
                assert(cost as int == Self::total_cost(nums@, k as int, dd as int));
            }

            let old_best = best;
            if dd == 0 || cost < best {
                best = cost;
                best_d = dd;
            }

            proof {
                let dn: int = dd as int;
                if dd == 0 || cost < old_best {
                    assert(best == Self::total_cost(nums@, k as int, dn));
                    assert(best_d as int == dn);
                    if dd > 0 {
                        assert(forall |d2: int| 0 <= d2 < dn ==> old_best <= Self::total_cost(nums@, k as int, d2));
                        assert(cost < old_best);
                        assert(forall |d2: int| 0 <= d2 < dn ==> best <= Self::total_cost(nums@, k as int, d2));
                    }
                } else {
                    assert(forall |d2: int| 0 <= d2 < dn ==> old_best <= Self::total_cost(nums@, k as int, d2));
                    assert(best == old_best);
                    assert(0 <= best_d < dd && best == Self::total_cost(nums@, k as int, best_d as int));
                    assert(best <= Self::total_cost(nums@, k as int, dn));
                }
            }

            if dd == 0 || cost < old_best {
                assert(best_d == dd);
            } else {
                assert(best_d < dd);
            }
            assert(dd < k + 1);
            assert(best_d < dd + 1);
            assert(dd + 1 <= k + 1);
            assert(k + 1 <= 100001);
            assert(dd + 1 <= 2147483647);
            dd += 1;
        }

        min_changes = best;

        if min_changes < 0 { 0 } else { min_changes }
    }
}

}
