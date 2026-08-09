use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn best(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

pub open spec fn best3(a: int, b: int, c: int) -> int {
    best(a, best(b, c))
}

pub open spec fn interval_ops(nums: Seq<i32>, l: int, r: int, target: int) -> int
    decreases if l <= r { r - l + 1 } else { 0 },
{
    if l >= r {
        0
    } else {
        let a = if l + 1 <= r && (nums[l] as int + nums[l + 1] as int == target) {
            1 + interval_ops(nums, l + 2, r, target)
        } else {
            0
        };
        let b = if nums[l] as int + nums[r] as int == target {
            1 + interval_ops(nums, l + 1, r - 1, target)
        } else {
            0
        };
        let c = if l <= r - 1 && (nums[r - 1] as int + nums[r] as int == target) {
            1 + interval_ops(nums, l, r - 2, target)
        } else {
            0
        };
        best3(a, b, c)
    }
}

pub open spec fn max_operations_spec(nums: Seq<i32>) -> int {
    let n = nums.len() as int;
    let s1 = nums[0] as int + nums[1] as int;
    let s2 = nums[0] as int + nums[n - 1] as int;
    let s3 = nums[n - 2] as int + nums[n - 1] as int;
    best3(
        1 + interval_ops(nums, 2, n - 1, s1),
        1 + interval_ops(nums, 1, n - 2, s2),
        1 + interval_ops(nums, 0, n - 3, s3),
    )
}

proof fn lemma_interval_ops_bound(nums: Seq<i32>, l: int, r: int, target: int)
    requires 0 <= l, r < nums.len(),
    ensures 0 <= interval_ops(nums, l, r, target) <= (if l <= r { r - l + 1 } else { 0 }),
    decreases if l <= r { r - l + 1 } else { 0 },
{
    if l < r {
        if l + 1 <= r {
            lemma_interval_ops_bound(nums, l + 2, r, target);
        }
        lemma_interval_ops_bound(nums, l + 1, r - 1, target);
        if l <= r - 1 {
            lemma_interval_ops_bound(nums, l, r - 2, target);
        }
    }
}

proof fn lemma_max_operations_spec_small(nums: Seq<i32>)
    requires 2 <= nums.len() <= 3,
    ensures max_operations_spec(nums) == 1,
{
    let n = nums.len() as int;
    assert(interval_ops(nums, 2, n - 1, nums[0] as int + nums[1] as int) == 0);
    assert(interval_ops(nums, 1, n - 2, nums[0] as int + nums[n - 1] as int) == 0);
    assert(interval_ops(nums, 0, n - 3, nums[n - 2] as int + nums[n - 1] as int) == 0);
}

proof fn lemma_flat_index_injective(n: int, l: int, r: int, l2: int, r2: int)
    requires
        0 <= l < n, 0 <= r < n, 0 <= l2 < n, 0 <= r2 < n,
        l * n + r == l2 * n + r2,
    ensures l == l2 && r == r2,
{
    if l != l2 {
        if l < l2 {
            assert((l2 - l) * n == r - r2) by (nonlinear_arith)
                requires l * n + r == l2 * n + r2;
            assert(l2 - l >= 1);
            assert((l2 - l) * n >= n) by (nonlinear_arith)
                requires l2 - l >= 1, n >= 1;
            assert(false);
        } else {
            assert((l - l2) * n == r2 - r) by (nonlinear_arith)
                requires l * n + r == l2 * n + r2;
            assert(l - l2 >= 1);
            assert((l - l2) * n >= n) by (nonlinear_arith)
                requires l - l2 >= 1, n >= 1;
            assert(false);
        }
    }
}

fn best_exec(a: i32, b: i32) -> (result: i32)
    ensures result as int == best(a as int, b as int),
{
    if a >= b { a } else { b }
}

fn best3_exec(a: i32, b: i32, c: i32) -> (result: i32)
    ensures result as int == best3(a as int, b as int, c as int),
{
    best_exec(a, best_exec(b, c))
}

fn solve_fixed(nums: &Vec<i32>, target: i32) -> (dp: Vec<i32>)
    requires
        2 <= nums.len() <= 2000,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
    ensures
        dp.len() == nums.len() * nums.len(),
        forall |l: int, r: int| 0 <= l <= r < nums.len() ==>
            #[trigger] dp[l * nums.len() as int + r] == interval_ops(nums@, l, r, target as int)
            && 0 <= dp[l * nums.len() as int + r] <= r - l + 1,
{
    let n = nums.len();
    proof {
        assert(n * n <= 2000 * 2000) by (nonlinear_arith)
            requires n <= 2000;
    }
    let nn: usize = n * n;
    let mut dp: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    while idx < nn
        invariant
            idx <= nn,
            nn == n * n,
            dp.len() == idx,
            forall |k: int| 0 <= k < idx as int ==> dp[k] == 0,
        decreases nn - idx,
    {
        dp.push(0);
        idx += 1;
    }
    proof {
        assert forall |l: int, r: int| 0 <= l <= r < n as int && r - l + 1 < 2 implies
            #[trigger] dp[l * n as int + r] == interval_ops(nums@, l, r, target as int) by {
            assert(l == r);
            assert(l * n as int + l < n as int * n as int) by (nonlinear_arith)
                requires 0 <= l < n as int;
            assert(dp[l * n as int + r] == 0);
            assert(interval_ops(nums@, l, r, target as int) == 0);
        }
    }
    let mut len: usize = 2;
    while len <= n
        invariant
            2 <= len <= n + 1,
            n <= 2000,
            n == nums.len(),
            forall |i: int| 0 <= i < n as int ==> 1 <= #[trigger] nums[i] <= 1000,
            nn == n * n,
            dp.len() == nn,
            forall |l: int, r: int| 0 <= l <= r < n as int && r - l + 1 < len as int ==>
                #[trigger] dp[l * n as int + r] == interval_ops(nums@, l, r, target as int),
        decreases n + 1 - len,
    {
        let bound: usize = n - len;
        let mut l: usize = 0;
        while l <= bound
            invariant
                l <= bound + 1,
                bound == n - len,
                bound <= 2000,
                n <= 2000,
                n == nums.len(),
                forall |i: int| 0 <= i < n as int ==> 1 <= #[trigger] nums[i] <= 1000,
                2 <= len <= n,
                nn == n * n,
                dp.len() == nn,
                forall |l2: int, r2: int| 0 <= l2 <= r2 < n as int
                    && (r2 - l2 + 1 < len as int
                        || (r2 - l2 + 1 == len as int && l2 < l as int)) ==>
                    #[trigger] dp[l2 * n as int + r2] == interval_ops(nums@, l2, r2, target as int),
            decreases (bound + 1) - l,
        {
            let r = l + len - 1;
            proof {
                assert(l < n);
                assert(l + 1 <= r);
                assert(r < n);
                assert(r >= 1);
            }
            proof {
                if len > 3 {
                    assert(l + 2 < n);
                    assert(r >= 2);
                }
            }
            let mut a: i32 = 0;
            if nums[l] + nums[l + 1] == target {
                let child: i32;
                if len > 3 {
                    proof {
                        assert((l + 2) * n + r < nn) by (nonlinear_arith)
                            requires l + 2 < n, r < n, nn == n * n;
                    }
                    child = dp[(l + 2) * n + r];
                    proof {
                        assert((l + 2) * n + r == (l as int + 2) * n as int + r as int) by (nonlinear_arith);
                        assert(child as int == interval_ops(nums@, l as int + 2, r as int, target as int));
                        lemma_interval_ops_bound(nums@, l as int + 2, r as int, target as int);
                        assert(child as int <= r as int - (l as int + 2) + 1);
                    }
                } else {
                    child = 0;
                    proof {
                        assert(l as int + 2 >= r as int);
                        assert(interval_ops(nums@, l as int + 2, r as int, target as int) == 0);
                    }
                }
                proof {
                    assert(child as int <= n as int);
                }
                a = 1 + child;
            }
            let mut b: i32 = 0;
            if nums[l] + nums[r] == target {
                let child: i32;
                if len > 3 {
                    proof {
                        assert((l + 1) * n + (r - 1) < nn) by (nonlinear_arith)
                            requires l + 1 < n, r - 1 < n, nn == n * n;
                    }
                    child = dp[(l + 1) * n + (r - 1)];
                    proof {
                        assert((l + 1) * n + (r - 1) == (l as int + 1) * n as int + (r as int - 1))
                            by (nonlinear_arith);
                        assert(child as int == interval_ops(nums@, l as int + 1, r as int - 1, target as int));
                        lemma_interval_ops_bound(nums@, l as int + 1, r as int - 1, target as int);
                        assert(child as int <= (r as int - 1) - (l as int + 1) + 1);
                    }
                } else {
                    child = 0;
                    proof {
                        assert(interval_ops(nums@, l as int + 1, r as int - 1, target as int) == 0);
                    }
                }
                proof {
                    assert(child as int <= n as int);
                }
                b = 1 + child;
            }
            let mut c: i32 = 0;
            if nums[r - 1] + nums[r] == target {
                let child: i32;
                if len > 3 {
                    proof {
                        assert(l * n + (r - 2) < nn) by (nonlinear_arith)
                            requires l < n, r - 2 < n, nn == n * n;
                    }
                    child = dp[l * n + (r - 2)];
                    proof {
                        assert(l * n + (r - 2) == l as int * n as int + (r as int - 2)) by (nonlinear_arith);
                        assert(child as int == interval_ops(nums@, l as int, r as int - 2, target as int));
                        lemma_interval_ops_bound(nums@, l as int, r as int - 2, target as int);
                        assert(child as int <= (r as int - 2) - l as int + 1);
                    }
                } else {
                    child = 0;
                    proof {
                        assert(interval_ops(nums@, l as int, r as int - 2, target as int) == 0);
                    }
                }
                proof {
                    assert(child as int <= n as int);
                }
                c = 1 + child;
            }
            let val = best3_exec(a, b, c);
            proof {
                assert(val as int == best3(a as int, b as int, c as int));
                assert(interval_ops(nums@, l as int, r as int, target as int)
                    == best3(a as int, b as int, c as int));
            }
            let ghost dp_before = dp@;
            proof {
                assert(l * n + r < nn) by (nonlinear_arith)
                    requires l < n, r < n, nn == n * n;
            }
            dp.set(l * n + r, val);
            proof {
                assert(l * n + r == l as int * n as int + r as int) by (nonlinear_arith);
                assert(dp@ == dp_before.update(l as int * n as int + r as int, val));
                assert forall |l2: int, r2: int| 0 <= l2 <= r2 < n as int
                    && (r2 - l2 + 1 < len as int
                        || (r2 - l2 + 1 == len as int && l2 < (l + 1) as int)) implies
                    #[trigger] dp[l2 * n as int + r2] == interval_ops(nums@, l2, r2, target as int) by {
                    if l2 == l as int && r2 == r as int {
                    } else {
                        if l2 * n as int + r2 == l as int * n as int + r as int {
                            lemma_flat_index_injective(n as int, l as int, r as int, l2, r2);
                            assert(false);
                        }
                        assert(l2 * n as int + r2 < nn as int) by (nonlinear_arith)
                            requires l2 < n as int, r2 < n as int, nn == n * n;
                        assert(dp[l2 * n as int + r2] == dp_before[l2 * n as int + r2]);
                    }
                }
            }
            l += 1;
        }
        len += 1;
    }
    proof {
        assert forall |l: int, r: int| 0 <= l <= r < n as int implies
            0 <= #[trigger] dp[l * n as int + r] <= r - l + 1 by {
            lemma_interval_ops_bound(nums@, l, r, target as int);
        }
    }
    dp
}

impl Solution {
    pub fn max_operations(nums: Vec<i32>) -> (result: i32)
        requires
            2 <= nums.len() <= 2000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
        ensures
            result as int == max_operations_spec(nums@),
    {
        let n = nums.len();
        if n <= 3 {
            proof {
                lemma_max_operations_spec_small(nums@);
            }
            return 1;
        }
        let s1 = nums[0] + nums[1];
        let s2 = nums[0] + nums[n - 1];
        let s3 = nums[n - 2] + nums[n - 1];
        let dp1 = solve_fixed(&nums, s1);
        let dp2 = solve_fixed(&nums, s2);
        let dp3 = solve_fixed(&nums, s3);
        proof {
            assert(dp1[2 * n as int + (n as int - 1)] == interval_ops(nums@, 2, n as int - 1, s1 as int)
                && dp1[2 * n as int + (n as int - 1)] <= n as int - 1 - 2 + 1);
            assert(dp2[1 * n as int + (n as int - 2)] == interval_ops(nums@, 1, n as int - 2, s2 as int)
                && dp2[1 * n as int + (n as int - 2)] <= n as int - 2 - 1 + 1);
            assert(dp3[0 * n as int + (n as int - 3)] == interval_ops(nums@, 0, n as int - 3, s3 as int)
                && dp3[0 * n as int + (n as int - 3)] <= n as int - 3 - 0 + 1);
            assert(2 * n + (n - 1) < n * n) by (nonlinear_arith)
                requires n >= 4;
            assert(1 * n + (n - 2) < n * n) by (nonlinear_arith)
                requires n >= 4;
            assert(0 * n + (n - 3) < n * n) by (nonlinear_arith)
                requires n >= 4;
            assert(2 * n as int + (n as int - 1) == 2 * n + (n - 1));
            assert(1 * n as int + (n as int - 2) == 1 * n + (n - 2));
            assert(0 * n as int + (n as int - 3) == 0 * n + (n - 3));
        }
        let a = 1 + dp1[2 * n + (n - 1)];
        let b = 1 + dp2[1 * n + (n - 2)];
        let c = 1 + dp3[0 * n + (n - 3)];
        let ans = best3_exec(a, b, c);
        proof {
            assert(ans as int == best3(a as int, b as int, c as int));
        }
        ans
    }
}

}
