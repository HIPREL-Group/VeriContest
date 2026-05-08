use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn abs_diff(a: int, b: int) -> int {
        if a >= b { a - b } else { b - a }
    }

    pub open spec fn move_cost(nums: Seq<i32>, cost: Seq<i32>, target: int, n: int) -> int
        recommends
            nums.len() == cost.len(),
            0 <= n && n <= nums.len(),
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            Self::move_cost(nums, cost, target, n - 1)
                + Self::abs_diff(nums[n - 1] as int, target) * cost[n - 1] as int
        }
    }

    pub open spec fn total_weight(cost: Seq<i32>, n: int) -> int
        recommends
            0 <= n && n <= cost.len(),
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            Self::total_weight(cost, n - 1) + cost[n - 1] as int
        }
    }

    pub open spec fn bucket_weight(nums: Seq<i32>, cost: Seq<i32>, value: int, n: int) -> int
        recommends
            nums.len() == cost.len(),
            0 <= n && n <= nums.len(),
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            Self::bucket_weight(nums, cost, value, n - 1)
                + if nums[n - 1] as int == value { cost[n - 1] as int } else { 0 }
        }
    }

    pub open spec fn prefix_weight(nums: Seq<i32>, cost: Seq<i32>, target: int, n: int) -> int
        recommends
            nums.len() == cost.len(),
            0 <= n && n <= nums.len(),
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            Self::prefix_weight(nums, cost, target, n - 1)
                + if nums[n - 1] as int <= target { cost[n - 1] as int } else { 0 }
        }
    }

    proof fn lemma_total_weight_step(cost: Seq<i32>, n: int)
        requires
            0 <= n && n < cost.len(),
        ensures
            Self::total_weight(cost, n + 1) == Self::total_weight(cost, n) + cost[n] as int,
    {
        reveal_with_fuel(Solution::total_weight, 2);
    }

    proof fn lemma_bucket_step(nums: Seq<i32>, cost: Seq<i32>, value: int, n: int)
        requires
            nums.len() == cost.len(),
            0 <= n && n < nums.len(),
        ensures
            Self::bucket_weight(nums, cost, value, n + 1)
                == Self::bucket_weight(nums, cost, value, n)
                    + if nums[n] as int == value { cost[n] as int } else { 0 },
    {
        reveal_with_fuel(Solution::bucket_weight, 2);
    }

    proof fn lemma_move_cost_extend(nums: Seq<i32>, cost: Seq<i32>, target: int, n: int)
        requires
            nums.len() == cost.len(),
            0 <= n && n < nums.len(),
        ensures
            Self::move_cost(nums, cost, target, n + 1)
                == Self::move_cost(nums, cost, target, n)
                    + Self::abs_diff(nums[n] as int, target) * cost[n] as int,
    {
        reveal_with_fuel(Solution::move_cost, 2);
    }

    proof fn lemma_move_cost_nonnegative(nums: Seq<i32>, cost: Seq<i32>, target: int, n: int)
        requires
            nums.len() == cost.len(),
            0 <= n && n <= nums.len(),
            forall|i: int| 0 <= i && i < n ==> 1 <= cost[i],
        ensures
            0 <= Self::move_cost(nums, cost, target, n),
        decreases n,
    {
        if n > 0 {
            Self::lemma_move_cost_nonnegative(nums, cost, target, n - 1);
            reveal_with_fuel(Solution::move_cost, 2);
            reveal(Solution::abs_diff);
        }
    }

    proof fn lemma_move_cost_bounded(nums: Seq<i32>, cost: Seq<i32>, target: int, n: int)
        requires
            nums.len() == cost.len(),
            0 <= n && n <= nums.len(),
            1 <= target && target <= 1_000_000,
            forall|i: int| 0 <= i && i < n ==> 1 <= nums[i] && nums[i] <= 1_000_000,
            forall|i: int| 0 <= i && i < n ==> 1 <= cost[i] && cost[i] <= 1_000_000,
        ensures
            Self::move_cost(nums, cost, target, n) <= n * 1_000_000_000_000int,
        decreases n,
    {
        if n > 0 {
            let k = n - 1;
            Self::lemma_move_cost_bounded(nums, cost, target, k);
            Self::lemma_move_cost_extend(nums, cost, target, k);
            reveal(Solution::abs_diff);
            assert(Self::abs_diff(nums[k] as int, target) <= 1_000_000);
            assert(Self::abs_diff(nums[k] as int, target) * cost[k] as int <= 1_000_000_000_000int) by (nonlinear_arith)
                requires
                    Self::abs_diff(nums[k] as int, target) <= 1_000_000,
                    cost[k] as int <= 1_000_000,
            {};
            assert(Self::move_cost(nums, cost, target, n) <= n * 1_000_000_000_000int) by (nonlinear_arith)
                requires
                    n == k + 1,
                    Self::move_cost(nums, cost, target, k) <= k * 1_000_000_000_000int,
                    Self::move_cost(nums, cost, target, n) == Self::move_cost(nums, cost, target, k) + Self::abs_diff(nums[k] as int, target) * cost[k] as int,
                    Self::abs_diff(nums[k] as int, target) * cost[k] as int <= 1_000_000_000_000int,
            {};
        }
    }

    proof fn lemma_prefix_bounded(nums: Seq<i32>, cost: Seq<i32>, target: int, n: int)
        requires
            nums.len() == cost.len(),
            0 <= n && n <= nums.len(),
            forall|i: int| 0 <= i && i < n ==> 1 <= cost[i],
        ensures
            0 <= Self::prefix_weight(nums, cost, target, n) <= Self::total_weight(cost, n),
        decreases n,
    {
        if n > 0 {
            Self::lemma_prefix_bounded(nums, cost, target, n - 1);
            Self::lemma_total_weight_step(cost, n - 1);
            reveal_with_fuel(Solution::prefix_weight, 2);
        }
    }

    proof fn lemma_prefix_zero(nums: Seq<i32>, cost: Seq<i32>, n: int)
        requires
            nums.len() == cost.len(),
            0 <= n && n <= nums.len(),
            forall|i: int| 0 <= i && i < n ==> 1 <= nums[i],
        ensures
            Self::prefix_weight(nums, cost, 0, n) == 0,
        decreases n,
    {
        if n > 0 {
            Self::lemma_prefix_zero(nums, cost, n - 1);
            reveal_with_fuel(Solution::prefix_weight, 2);
        }
    }

    proof fn lemma_prefix_bucket_step(nums: Seq<i32>, cost: Seq<i32>, target: int, n: int)
        requires
            nums.len() == cost.len(),
            0 <= n && n <= nums.len(),
            forall|i: int| 0 <= i && i < n ==> 1 <= nums[i] && nums[i] <= 1_000_000,
            0 <= target && target < 1_000_000,
        ensures
            Self::prefix_weight(nums, cost, target + 1, n)
                == Self::prefix_weight(nums, cost, target, n)
                    + Self::bucket_weight(nums, cost, target + 1, n),
        decreases n,
    {
        if n > 0 {
            Self::lemma_prefix_bucket_step(nums, cost, target, n - 1);
            reveal_with_fuel(Solution::prefix_weight, 2);
            reveal_with_fuel(Solution::bucket_weight, 2);
            let a = nums[n - 1] as int;
            let w = cost[n - 1] as int;
            if a <= target {
                assert(a != target + 1);
            } else if a == target + 1 {
            } else {
                assert(target + 1 < a);
            }
            assert((if a <= target + 1 { w } else { 0 })
                == (if a <= target { w } else { 0 }) + (if a == target + 1 { w } else { 0 }));
        }
    }

    proof fn lemma_abs_step(a: int, target: int)
        requires
            1 <= a && a <= 1_000_000,
            1 <= target && target < 1_000_000,
        ensures
            Self::abs_diff(a, target + 1)
                == Self::abs_diff(a, target) + if a <= target { 1 } else { -1 },
    {
        reveal(Solution::abs_diff);
        if a <= target {
            assert(Self::abs_diff(a, target + 1) == target + 1 - a);
            assert(Self::abs_diff(a, target) == target - a);
        } else {
            assert(target + 1 <= a);
            assert(Self::abs_diff(a, target + 1) == a - (target + 1));
            assert(Self::abs_diff(a, target) == a - target);
        }
    }

    proof fn lemma_cost_target_step(nums: Seq<i32>, cost: Seq<i32>, target: int, n: int)
        requires
            nums.len() == cost.len(),
            0 <= n && n <= nums.len(),
            forall|i: int| 0 <= i && i < n ==> 1 <= nums[i] && nums[i] <= 1_000_000,
            forall|i: int| 0 <= i && i < n ==> 1 <= cost[i] && cost[i] <= 1_000_000,
            1 <= target && target < 1_000_000,
        ensures
            Self::move_cost(nums, cost, target + 1, n)
                == Self::move_cost(nums, cost, target, n)
                    + Self::prefix_weight(nums, cost, target, n)
                    - (Self::total_weight(cost, n) - Self::prefix_weight(nums, cost, target, n)),
        decreases n,
    {
        if n > 0 {
            let k = n - 1;
            Self::lemma_cost_target_step(nums, cost, target, k);
            Self::lemma_move_cost_extend(nums, cost, target + 1, k);
            Self::lemma_move_cost_extend(nums, cost, target, k);
            Self::lemma_total_weight_step(cost, k);
            reveal_with_fuel(Solution::prefix_weight, 2);
            let a = nums[k] as int;
            let w = cost[k] as int;
            Self::lemma_abs_step(a, target);
            if a <= target {
                assert((if a <= target { w } else { 0 }) == w);
            } else {
                assert((if a <= target { w } else { 0 }) == 0);
            }
            assert(Self::abs_diff(a, target + 1) * w
                == Self::abs_diff(a, target) * w + (if a <= target { w } else { -w })) by (nonlinear_arith)
                requires
                    Self::abs_diff(a, target + 1)
                        == Self::abs_diff(a, target) + if a <= target { 1 } else { -1 },
                    1 <= w,
            {};
            assert((if a <= target { w } else { -w })
                == (if a <= target { w } else { 0 }) - (w - (if a <= target { w } else { 0 })));
        }
    }

    proof fn lemma_prefix_one(nums: Seq<i32>, cost: Seq<i32>, n: int)
        requires
            nums.len() == cost.len(),
            0 <= n && n <= nums.len(),
            forall|i: int| 0 <= i && i < n ==> 1 <= nums[i] && nums[i] <= 1_000_000,
        ensures
            Self::prefix_weight(nums, cost, 1, n) == Self::bucket_weight(nums, cost, 1, n),
    {
        Self::lemma_prefix_zero(nums, cost, n);
        Self::lemma_prefix_bucket_step(nums, cost, 0, n);
        assert(Self::prefix_weight(nums, cost, 1, n)
            == Self::prefix_weight(nums, cost, 0, n) + Self::bucket_weight(nums, cost, 1, n));
    }

    pub fn min_cost(nums: Vec<i32>, cost: Vec<i32>) -> (result: i64)
        requires
            1 <= nums.len() && nums.len() <= 100_000,
            nums.len() == cost.len(),
            forall|i: int| 0 <= i && i < nums.len() ==> 1 <= nums[i] && nums[i] <= 1_000_000,
            forall|i: int| 0 <= i && i < cost.len() ==> 1 <= cost[i] && cost[i] <= 1_000_000,
        ensures
            result >= 0,
            forall|target: int| 1 <= target && target <= 1_000_000 ==> result as int <= #[trigger] Self::move_cost(nums@, cost@, target, nums.len() as int),
            exists|target: int| 1 <= target && target <= 1_000_000 && result as int == Self::move_cost(nums@, cost@, target, nums.len() as int),
    {
        let max_value: usize = 1_000_000;
        let n = nums.len();
        let mut weights: Vec<i64> = Vec::new();
        let mut zeroes: usize = 0;

        while zeroes < max_value + 1
            invariant
                max_value == 1_000_000,
                weights@.len() == zeroes as int,
                0 <= zeroes && zeroes <= max_value + 1,
                forall|j: int| 0 <= j && j < zeroes as int ==> #[trigger] weights@[j] == 0,
            decreases max_value + 1 - zeroes,
        {
            weights.push(0);
            zeroes = zeroes + 1;
        }

        let mut total_weight: i64 = 0;
        let mut current: i64 = 0;
        let mut i: usize = 0;

        proof {
            reveal_with_fuel(Solution::total_weight, 1);
            reveal_with_fuel(Solution::move_cost, 1);
            assert(forall|v: int| 1 <= v && v <= max_value as int ==> (#[trigger] weights@[v]) as int == Self::bucket_weight(nums@, cost@, v, 0)) by {
                let v: int = arbitrary();
                reveal_with_fuel(Solution::bucket_weight, 1);
            }
        }

        while i < n
            invariant
                max_value == 1_000_000,
                n == nums.len(),
                n == cost.len(),
                1 <= n && n <= 100_000,
                weights.len() == max_value + 1,
                weights@[0] == 0,
                forall|j: int| 0 <= j && j < n as int ==> 1 <= nums@[j] && nums@[j] <= 1_000_000,
                forall|j: int| 0 <= j && j < n as int ==> 1 <= cost@[j] && cost@[j] <= 1_000_000,
                0 <= i && i <= n,
                0 <= total_weight as int <= i as int * 1_000_000,
                0 <= current as int <= i as int * 1_000_000_000_000,
                total_weight as int == Self::total_weight(cost@, i as int),
                current as int == Self::move_cost(nums@, cost@, 1, i as int),
                forall|v: int| 1 <= v && v <= max_value as int ==> (#[trigger] weights@[v]) as int == Self::bucket_weight(nums@, cost@, v, i as int),
                forall|v: int| 0 <= v && v <= max_value as int ==> 0 <= (#[trigger] weights@[v]) as int <= total_weight as int,
            decreases n - i,
        {
            let value = nums[i] as usize;
            let c = cost[i] as i64;
            let prev_bucket = weights[value];
            let ghost prev_weights = weights@;
            let ghost k = i as int;

            proof {
                assert(1 <= nums@[k] && nums@[k] <= 1_000_000);
                assert(1 <= cost@[k] && cost@[k] <= 1_000_000);
                assert(1 <= value as int && value as int <= max_value as int);
                assert(0 <= prev_bucket as int <= total_weight as int);
                assert(prev_bucket as int + c as int <= (k + 1) * 1_000_000) by (nonlinear_arith)
                    requires
                        prev_bucket as int <= total_weight as int,
                        total_weight as int <= k * 1_000_000,
                        c as int <= 1_000_000,
                {};
                assert((nums@[k] as int - 1) * c as int <= 1_000_000_000_000) by (nonlinear_arith)
                    requires
                    nums@[k] as int <= 1_000_000,
                        c as int <= 1_000_000,
                    1 <= nums@[k] as int,
                {};
                assert(current as int + (nums@[k] as int - 1) * c as int <= (k + 1) * 1_000_000_000_000) by (nonlinear_arith)
                    requires
                        current as int <= k * 1_000_000_000_000,
                    (nums@[k] as int - 1) * c as int <= 1_000_000_000_000,
                {};
            }

            weights.set(value, weights[value] + c);
            total_weight = total_weight + c;
            current = current + (nums[i] as i64 - 1) * c;

            proof {
                Self::lemma_bucket_step(nums@, cost@, value as int, k);
                Self::lemma_total_weight_step(cost@, k);
                Self::lemma_move_cost_extend(nums@, cost@, 1, k);
                assert(total_weight as int == Self::total_weight(cost@, k + 1));
                assert(current as int == Self::move_cost(nums@, cost@, 1, k + 1));
                assert(weights@[0] == 0);
                assert(forall|v: int| 1 <= v && v <= max_value as int ==> (#[trigger] weights@[v]) as int == Self::bucket_weight(nums@, cost@, v, k + 1)) by {
                    let v: int = arbitrary();
                    if 1 <= v && v <= max_value as int {
                        assert(0 <= v && v < weights@.len());
                        assert(0 <= v && v < prev_weights.len());
                        if v == value as int {
                            assert(weights@[v] as int == prev_weights[v] as int + c as int);
                            assert(prev_weights[v] as int == Self::bucket_weight(nums@, cost@, v, k));
                        } else {
                            assert(weights@[v] == prev_weights[v]);
                        }
                    }
                }
                assert(forall|v: int| 0 <= v && v <= max_value as int ==> 0 <= (#[trigger] weights@[v]) as int <= total_weight as int) by {
                    let v: int = arbitrary();
                    if 0 <= v && v <= max_value as int {
                        assert(v < weights@.len());
                        assert(v < prev_weights.len());
                        if v == value as int {
                            assert(weights@[v] as int == prev_weights[v] as int + c as int);
                        } else {
                            assert(weights@[v] == prev_weights[v]);
                        }
                    }
                }
            }

            i = i + 1;
        }

        let mut target: usize = 1;
        let mut prefix: i64 = weights[1];
        let mut best: i64 = current;
        let ghost mut best_target: int = 1;

        proof {
            Self::lemma_prefix_one(nums@, cost@, n as int);
            assert(prefix as int == Self::prefix_weight(nums@, cost@, 1, n as int));
            assert(best as int == Self::move_cost(nums@, cost@, best_target, n as int));
            assert(forall|u: int| 1 <= u && u <= target as int ==> best as int <= #[trigger] Self::move_cost(nums@, cost@, u, n as int)) by {
                let u: int = arbitrary();
                if 1 <= u && u <= target as int {
                    assert(u == 1);
                }
            }
        }

        while target < max_value
            invariant
                max_value == 1_000_000,
                n == nums.len(),
                n == cost.len(),
                1 <= n && n <= 100_000,
                weights.len() == max_value + 1,
                weights@[0] == 0,
                forall|j: int| 0 <= j && j < n as int ==> 1 <= nums@[j] && nums@[j] <= 1_000_000,
                forall|j: int| 0 <= j && j < n as int ==> 1 <= cost@[j] && cost@[j] <= 1_000_000,
                total_weight as int == Self::total_weight(cost@, n as int),
                0 <= total_weight as int <= n as int * 1_000_000,
                forall|v: int| 1 <= v && v <= max_value as int ==> (#[trigger] weights@[v]) as int == Self::bucket_weight(nums@, cost@, v, n as int),
                forall|v: int| 0 <= v && v <= max_value as int ==> 0 <= (#[trigger] weights@[v]) as int <= total_weight as int,
                1 <= target && target <= max_value,
                prefix as int == Self::prefix_weight(nums@, cost@, target as int, n as int),
                0 <= prefix as int <= total_weight as int,
                current as int == Self::move_cost(nums@, cost@, target as int, n as int),
                0 <= current as int <= 100_000_000_000_000_000,
                1 <= best_target && best_target <= target as int,
                best as int == Self::move_cost(nums@, cost@, best_target, n as int),
                0 <= best as int <= 100_000_000_000_000_000,
                forall|u: int| 1 <= u && u <= target as int ==> best as int <= #[trigger] Self::move_cost(nums@, cost@, u, n as int),
            decreases max_value - target,
        {
            let old_best = best;
            let ghost old_best_target = best_target;
            let ghost old_target = target as int;
            let delta = prefix - (total_weight - prefix);

            proof {
                Self::lemma_cost_target_step(nums@, cost@, old_target, n as int);
                assert(delta as int == 2 * prefix as int - total_weight as int) by (nonlinear_arith)
                    requires
                        delta as int == prefix as int - (total_weight as int - prefix as int),
                {};
                assert(-(total_weight as int) <= delta as int) by (nonlinear_arith)
                    requires
                        delta as int == 2 * prefix as int - total_weight as int,
                        0 <= prefix as int,
                        prefix as int <= total_weight as int,
                {};
                assert(delta as int <= total_weight as int) by (nonlinear_arith)
                    requires
                        delta as int == 2 * prefix as int - total_weight as int,
                        0 <= prefix as int,
                        prefix as int <= total_weight as int,
                {};
                assert(current as int + delta as int == Self::move_cost(nums@, cost@, old_target + 1, n as int));
                Self::lemma_move_cost_nonnegative(nums@, cost@, old_target + 1, n as int);
                Self::lemma_move_cost_bounded(nums@, cost@, old_target + 1, n as int);
                assert(0 <= current as int + delta as int);
                assert(current as int + delta as int <= 100_000_000_000_000_000);
            }

            current = current + delta;
            target = target + 1;

            proof {
                Self::lemma_prefix_bucket_step(nums@, cost@, old_target, n as int);
                assert(prefix as int + weights@[target as int] as int
                    == Self::prefix_weight(nums@, cost@, old_target, n as int)
                        + Self::bucket_weight(nums@, cost@, target as int, n as int));
                assert(prefix as int + weights@[target as int] as int
                    == Self::prefix_weight(nums@, cost@, target as int, n as int));
                Self::lemma_prefix_bounded(nums@, cost@, target as int, n as int);
            }

            prefix = prefix + weights[target];
            if current < best {
                best = current;
                proof {
                    best_target = target as int;
                }
            }

            proof {
                if current < old_best {
                    assert(best as int == Self::move_cost(nums@, cost@, best_target, n as int));
                } else {
                    assert(best == old_best);
                    assert(best_target == old_best_target);
                }
                assert(forall|u: int| 1 <= u && u <= target as int ==> best as int <= #[trigger] Self::move_cost(nums@, cost@, u, n as int)) by {
                    let u: int = arbitrary();
                    if 1 <= u && u <= target as int {
                        if u < target as int {
                            assert(u <= old_target);
                            if current < old_best {
                                assert(best == current);
                                assert(current < old_best);
                                assert(old_best as int <= Self::move_cost(nums@, cost@, u, n as int));
                            } else {
                                assert(best == old_best);
                            }
                        } else {
                            assert(u == target as int);
                            if current < old_best {
                                assert(best == current);
                            } else {
                                assert(best == old_best);
                                assert(old_best <= current);
                            }
                        }
                    }
                }
            }
        }

        proof {
            assert(forall|target0: int| 1 <= target0 && target0 <= 1_000_000 ==> best as int <= #[trigger] Self::move_cost(nums@, cost@, target0, n as int)) by {
                let target0: int = arbitrary();
            }
            assert(exists|target0: int| 1 <= target0 && target0 <= 1_000_000 && best as int == Self::move_cost(nums@, cost@, target0, n as int)) by {
                let witness = best_target;
                assert(1 <= witness && witness <= 1_000_000);
                assert(best as int == Self::move_cost(nums@, cost@, witness, n as int));
            }
        }

        best
    }
}

}
