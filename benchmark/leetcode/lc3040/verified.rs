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

proof fn lemma_interval_ops_step(nums: Seq<i32>, l: int, r: int, target: int)
    requires
        0 <= l <= nums.len(),
        -1 <= r < nums.len(),
        l <= r + 1,
    ensures
        interval_ops(nums, l, r, target) == if l >= r {
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
        },
{
    reveal_with_fuel(interval_ops, 2);
}

proof fn lemma_best3_bounds(a: int, b: int, c: int, lo: int, hi: int)
    requires
        lo <= a <= hi,
        lo <= b <= hi,
        lo <= c <= hi,
    ensures
        lo <= best3(a, b, c) <= hi,
{
    reveal(best3);
    reveal(best);
}

proof fn lemma_interval_ops_bound(nums: Seq<i32>, l: int, r: int, target: int)
    requires
        0 <= l <= nums.len(),
        -1 <= r < nums.len(),
        l <= r + 1,
    ensures
        0 <= interval_ops(nums, l, r, target),
        interval_ops(nums, l, r, target) <= if l <= r { r - l + 1 } else { 0 },
    decreases if l <= r { r - l + 1 } else { 0 },
{
    if l >= r {
        lemma_interval_ops_step(nums, l, r, target);
    } else {
        lemma_interval_ops_bound(nums, l + 2, r, target);
        lemma_interval_ops_bound(nums, l + 1, r - 1, target);
        lemma_interval_ops_bound(nums, l, r - 2, target);
        lemma_interval_ops_step(nums, l, r, target);

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

        assert(0 <= a);
        assert(0 <= b);
        assert(0 <= c);

        if l + 1 <= r && (nums[l] as int + nums[l + 1] as int == target) {
            assert(interval_ops(nums, l + 2, r, target) <= r - (l + 2) + 1);
            assert(a <= r - l + 1) by (nonlinear_arith)
                requires
                    a == 1 + interval_ops(nums, l + 2, r, target),
                    interval_ops(nums, l + 2, r, target) <= r - (l + 2) + 1;
        } else {
            assert(a == 0);
            assert(a <= r - l + 1);
        }

        if nums[l] as int + nums[r] as int == target {
            assert(interval_ops(nums, l + 1, r - 1, target) <= (r - 1) - (l + 1) + 1);
            assert(b <= r - l + 1) by (nonlinear_arith)
                requires
                    b == 1 + interval_ops(nums, l + 1, r - 1, target),
                    interval_ops(nums, l + 1, r - 1, target) <= (r - 1) - (l + 1) + 1;
        } else {
            assert(b == 0);
            assert(b <= r - l + 1);
        }

        if l <= r - 1 && (nums[r - 1] as int + nums[r] as int == target) {
            assert(interval_ops(nums, l, r - 2, target) <= (r - 2) - l + 1);
            assert(c <= r - l + 1) by (nonlinear_arith)
                requires
                    c == 1 + interval_ops(nums, l, r - 2, target),
                    interval_ops(nums, l, r - 2, target) <= (r - 2) - l + 1;
        } else {
            assert(c == 0);
            assert(c <= r - l + 1);
        }

        lemma_best3_bounds(a, b, c, 0, r - l + 1);
    }
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
                let ni = n as int;
                let s1 = nums@[0] as int + nums@[1] as int;
                let s2 = nums@[0] as int + nums@[ni - 1] as int;
                let s3 = nums@[ni - 2] as int + nums@[ni - 1] as int;
                lemma_interval_ops_step(nums@, 2, ni - 1, s1);
                lemma_interval_ops_step(nums@, 1, ni - 2, s2);
                lemma_interval_ops_step(nums@, 0, ni - 3, s3);
                assert(interval_ops(nums@, 2, ni - 1, s1) == 0);
                assert(interval_ops(nums@, 1, ni - 2, s2) == 0);
                assert(interval_ops(nums@, 0, ni - 3, s3) == 0);
                reveal(max_operations_spec);
                assert(best3(1, 1, 1) == 1);
            }
            return 1;
        }
        let s1 = nums[0] + nums[1];
        let s2 = nums[0] + nums[n - 1];
        let s3 = nums[n - 2] + nums[n - 1];
        let dp1 = Self::solve_fixed(&nums, s1);
        let dp2 = Self::solve_fixed(&nums, s2);
        let dp3 = Self::solve_fixed(&nums, s3);
        assert(2 < dp1.len());
        assert(1 < dp2.len());
        assert(0 < dp3.len());
        assert((n - 1) < dp1[2].len());
        assert((n - 2) < dp2[1].len());
        assert((n - 3) < dp3[0].len());
        proof {
            let ni = n as int;
            lemma_interval_ops_bound(nums@, 2, ni - 1, s1 as int);
            lemma_interval_ops_bound(nums@, 1, ni - 2, s2 as int);
            lemma_interval_ops_bound(nums@, 0, ni - 3, s3 as int);
            assert(dp1@[2][(n - 1) as int] as int == interval_ops(nums@, 2, ni - 1, s1 as int));
            assert(dp2@[1][(n - 2) as int] as int == interval_ops(nums@, 1, ni - 2, s2 as int));
            assert(dp3@[0][(n - 3) as int] as int == interval_ops(nums@, 0, ni - 3, s3 as int));
            assert(0 <= dp1@[2][(n - 1) as int] as int <= 2000);
            assert(0 <= dp2@[1][(n - 2) as int] as int <= 2000);
            assert(0 <= dp3@[0][(n - 3) as int] as int <= 2000);
        }
        assert(0 <= dp1[2][n - 1] <= 2000);
        assert(0 <= dp2[1][n - 2] <= 2000);
        assert(0 <= dp3[0][n - 3] <= 2000);
        let a = 1 + dp1[2][n - 1];
        let b = 1 + dp2[1][n - 2];
        let c = 1 + dp3[0][n - 3];
        let ans = Self::best3_exec(a, b, c);
        proof {
            let ni = n as int;
            assert(4 <= n);
            assert(n <= 2000);
            assert(dp1@[2][(n - 1) as int] as int == interval_ops(nums@, 2, ni - 1, s1 as int));
            assert(dp2@[1][(n - 2) as int] as int == interval_ops(nums@, 1, ni - 2, s2 as int));
            assert(dp3@[0][(n - 3) as int] as int == interval_ops(nums@, 0, ni - 3, s3 as int));
            assert(a as int == 1 + interval_ops(nums@, 2, ni - 1, s1 as int));
            assert(b as int == 1 + interval_ops(nums@, 1, ni - 2, s2 as int));
            assert(c as int == 1 + interval_ops(nums@, 0, ni - 3, s3 as int));
            assert(ans as int == best3(a as int, b as int, c as int));
            reveal(max_operations_spec);
        }
        ans
    }

    fn solve_fixed(nums: &Vec<i32>, target: i32) -> (dp: Vec<Vec<i32>>)
        requires
            4 <= nums.len() <= 2000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
        ensures
            dp.len() == nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> #[trigger] dp[i].len() == nums.len(),
            forall |l: int, r: int| 0 <= l <= r < nums.len() ==> (#[trigger] dp[l][r]) as int == interval_ops(nums@, l, r, target as int),
    {
        let n = nums.len();
        let mut dp: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                n == nums.len(),
                4 <= n <= 2000,
                0 <= i <= n,
                dp.len() == i,
                forall |k: int| 0 <= k < i as int ==> #[trigger] dp[k].len() == n,
                forall |k: int, j: int| 0 <= k < i as int && 0 <= j < n as int ==> #[trigger] dp[k][j] == 0,
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 1000,
            decreases n - i,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < n
                invariant
                    n == nums.len(),
                    0 <= j <= n,
                    row.len() == j,
                    forall |t: int| 0 <= t < j as int ==> #[trigger] row[t] == 0,
                decreases n - j,
            {
                row.push(0);
                j = j + 1;
            }
            dp.push(row);
            i = i + 1;
        }

        let mut len: usize = 2;
        while len <= n
            invariant
                n == nums.len(),
                4 <= n <= 2000,
                dp.len() == n,
                forall |k: int| 0 <= k < n as int ==> #[trigger] dp[k].len() == n,
                2 <= len <= n + 1,
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 1000,
                forall |d: int| 0 <= d < n as int ==> #[trigger] dp[d][d] == 0,
                forall |l: int, r: int| 0 <= l <= r < n as int && 2 <= r - l + 1 < len as int ==> (#[trigger] dp[l][r]) as int == interval_ops(nums@, l, r, target as int),
            decreases n + 1 - len,
        {
            let mut l: usize = 0;
            while l + len <= n
                invariant
                    n == nums.len(),
                    4 <= n <= 2000,
                    dp.len() == n,
                    forall |k: int| 0 <= k < n as int ==> #[trigger] dp[k].len() == n,
                    2 <= len <= n,
                    0 <= l,
                    l + len <= n + 1,
                    forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 1000,
                    forall |d: int| 0 <= d < n as int ==> #[trigger] dp[d][d] == 0,
                    forall |ll: int, rr: int| 0 <= ll <= rr < n as int && 2 <= rr - ll + 1 < len as int ==> (#[trigger] dp[ll][rr]) as int == interval_ops(nums@, ll, rr, target as int),
                    forall |ll: int| 0 <= ll < l as int ==> (#[trigger] dp[ll][ll + len as int - 1]) as int == interval_ops(nums@, ll, ll + len as int - 1, target as int),
                decreases n - l,
            {
                let r = l + len - 1;
                let mut a: i32 = 0;
                if nums[l] + nums[l + 1] == target {
                    let child: i32;
                    if len > 3 {
                        assert(l + 2 < n);
                        assert(r < n);
                        assert(l + 2 < dp.len());
                        proof {
                            let li = (l + 2) as int;
                            assert(0 <= li < n as int);
                            assert(dp[li].len() == n);
                        }
                        child = dp[l + 2][r];
                    } else {
                        child = 0;
                    }
                    proof {
                        if len > 3 {
                            assert(2 <= (l + 2) as int);
                            assert((l + 2) as int <= r as int);
                            assert(r < n);
                            assert(2 <= r as int - (l + 2) as int + 1);
                            assert(r as int - (l + 2) as int + 1 < len as int);
                            assert(child as int == interval_ops(nums@, (l + 2) as int, r as int, target as int));
                            lemma_interval_ops_bound(nums@, (l + 2) as int, r as int, target as int);
                            assert(child <= 2000);
                        }
                    }
                    assert(0 <= child <= 2000);
                    a = 1 + child;
                }
                let mut b: i32 = 0;
                if nums[l] + nums[r] == target {
                    let child: i32;
                    if len > 3 {
                        assert(l + 1 < n);
                        assert(1 <= r);
                        assert(r - 1 < n);
                        assert(l + 1 < dp.len());
                        proof {
                            let li = (l + 1) as int;
                            assert(0 <= li < n as int);
                            assert(dp[li].len() == n);
                        }
                        child = dp[l + 1][r - 1];
                    } else {
                        child = 0;
                    }
                    proof {
                        if len > 3 {
                            assert(1 <= l as int + 1);
                            assert((l as int + 1) <= (r as int - 1));
                            assert(r - 1 < n);
                            assert(2 <= (r as int - 1) - (l as int + 1) + 1);
                            assert((r as int - 1) - (l as int + 1) + 1 < len as int);
                            assert(child as int == interval_ops(nums@, (l + 1) as int, (r - 1) as int, target as int));
                            lemma_interval_ops_bound(nums@, (l + 1) as int, (r - 1) as int, target as int);
                            assert(child <= 2000);
                        }
                    }
                    assert(0 <= child <= 2000);
                    b = 1 + child;
                }
                let mut c: i32 = 0;
                if nums[r - 1] + nums[r] == target {
                    let child: i32;
                    if len > 3 {
                        assert(2 <= r);
                        assert(l < n);
                        assert(r - 2 < n);
                        assert(l < dp.len());
                        proof {
                            let li = l as int;
                            assert(0 <= li < n as int);
                            assert(dp[li].len() == n);
                        }
                        child = dp[l][r - 2];
                    } else {
                        child = 0;
                    }
                    proof {
                        if len > 3 {
                            assert(0 <= l as int);
                            assert(l as int <= r as int - 2);
                            assert(r - 2 < n);
                            assert(2 <= (r as int - 2) - l as int + 1);
                            assert((r as int - 2) - l as int + 1 < len as int);
                            assert(child as int == interval_ops(nums@, l as int, (r - 2) as int, target as int));
                            lemma_interval_ops_bound(nums@, l as int, (r - 2) as int, target as int);
                            assert(child <= 2000);
                        }
                    }
                    assert(0 <= child <= 2000);
                    c = 1 + child;
                }
                let val = Self::best3_exec(a, b, c);
                let ghost old_dp = dp@;
                let mut row = dp[l].clone();
                row.set(r, val);
                dp.set(l, row);
                proof {
                    assert(0 <= l);
                    assert(l < n);
                    assert(0 <= r);
                    assert(r < n);
                    assert(l < r);
                    assert(r as int - l as int + 1 == len as int);
                    lemma_interval_ops_step(nums@, l as int, r as int, target as int);

                    if len > 3 {
                        assert(old_dp[(l + 2) as int][r as int] as int == interval_ops(nums@, (l + 2) as int, r as int, target as int));
                        assert(old_dp[(l + 1) as int][(r - 1) as int] as int == interval_ops(nums@, (l + 1) as int, (r - 1) as int, target as int));
                        assert(old_dp[l as int][(r - 2) as int] as int == interval_ops(nums@, l as int, (r - 2) as int, target as int));
                    } else {
                        lemma_interval_ops_step(nums@, (l + 2) as int, r as int, target as int);
                        lemma_interval_ops_step(nums@, (l + 1) as int, (r - 1) as int, target as int);
                        lemma_interval_ops_step(nums@, l as int, (r - 2) as int, target as int);
                        assert(interval_ops(nums@, (l + 2) as int, r as int, target as int) == 0);
                        assert(interval_ops(nums@, (l + 1) as int, (r - 1) as int, target as int) == 0);
                        assert(interval_ops(nums@, l as int, (r - 2) as int, target as int) == 0);
                    }

                    assert(a as int == if l as int + 1 <= r as int && (nums@[l as int] as int + nums@[l as int + 1] as int == target as int) {
                        1 + interval_ops(nums@, l as int + 2, r as int, target as int)
                    } else {
                        0
                    });
                    assert(b as int == if nums@[l as int] as int + nums@[r as int] as int == target as int {
                        1 + interval_ops(nums@, l as int + 1, r as int - 1, target as int)
                    } else {
                        0
                    });
                    assert(c as int == if l as int <= r as int - 1 && (nums@[r as int - 1] as int + nums@[r as int] as int == target as int) {
                        1 + interval_ops(nums@, l as int, r as int - 2, target as int)
                    } else {
                        0
                    });
                    assert(val as int == best3(a as int, b as int, c as int));
                    assert(val as int == interval_ops(nums@, l as int, r as int, target as int));

                    assert forall |d: int| 0 <= d < n as int implies #[trigger] dp[d][d] == 0 by {
                        if d != l as int {
                            assert(dp[d] == old_dp[d]);
                        } else {
                            assert((l as int) != r as int);
                            assert(dp[d][d] == old_dp[d][d]);
                        }
                    };

                    assert forall |ll: int, rr: int| 0 <= ll <= rr < n as int && 2 <= rr - ll + 1 < len as int implies (#[trigger] dp[ll][rr]) as int == interval_ops(nums@, ll, rr, target as int) by {
                        if ll != l as int {
                            assert(dp[ll] == old_dp[ll]);
                        } else {
                            assert(rr - ll + 1 < len as int);
                            assert(rr < r as int) by (nonlinear_arith)
                                requires
                                    ll == l as int,
                                    rr - ll + 1 < len as int,
                                    r as int == l as int + len as int - 1;
                            assert(dp[ll][rr] == old_dp[ll][rr]);
                        }
                    };

                    assert forall |ll: int| 0 <= ll < l as int + 1 implies (#[trigger] dp[ll][ll + len as int - 1]) as int == interval_ops(nums@, ll, ll + len as int - 1, target as int) by {
                        if ll != l as int {
                            assert(dp[ll] == old_dp[ll]);
                        } else {
                            assert(ll + len as int - 1 == r as int);
                            assert(dp[ll][ll + len as int - 1] as int == val as int);
                        }
                    };
                }
                l = l + 1;
            }
            proof {
                assert((n as int) < (l as int) + (len as int));
                assert forall |ll: int| 0 <= ll && ll + (len as int) - 1 < n as int implies
                    (#[trigger] dp[ll][ll + (len as int) - 1]) as int == interval_ops(nums@, ll, ll + (len as int) - 1, target as int) by {
                    assert(ll + (len as int) <= n as int);
                    assert(ll < l as int) by (nonlinear_arith)
                        requires
                            (n as int) < (l as int) + (len as int),
                            ll + (len as int) <= n as int;
                };
                assert forall |ll: int, rr: int| 0 <= ll <= rr < n as int && 2 <= rr - ll + 1 < (len as int) + 1 implies
                    (#[trigger] dp[ll][rr]) as int == interval_ops(nums@, ll, rr, target as int) by {
                    if rr - ll + 1 < len as int {
                    } else {
                        assert(rr - ll + 1 == len as int);
                        assert(rr == ll + (len as int) - 1) by (nonlinear_arith)
                            requires rr - ll + 1 == len as int;
                        assert((#[trigger] dp[ll][ll + (len as int) - 1]) as int == interval_ops(nums@, ll, ll + (len as int) - 1, target as int));
                    }
                };
            }
            len = len + 1;
        }
        proof {
            assert forall |l: int, r: int| 0 <= l <= r < nums.len() implies (#[trigger] dp[l][r]) as int == interval_ops(nums@, l, r, target as int) by {
                if l == r {
                    lemma_interval_ops_step(nums@, l, r, target as int);
                    assert(interval_ops(nums@, l, r, target as int) == 0);
                    assert(dp[l][r] == 0);
                }
            };
        }
        dp
    }

    fn best_exec(a: i32, b: i32) -> (c: i32)
        ensures
            c as int == best(a as int, b as int),
    {
        if a >= b { a } else { b }
    }

    fn best3_exec(a: i32, b: i32, c: i32) -> (d: i32)
        ensures
            d as int == best3(a as int, b as int, c as int),
    {
        Self::best_exec(a, Self::best_exec(b, c))
    }
}

}
