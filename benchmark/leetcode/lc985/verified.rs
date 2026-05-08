use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn even_contrib(x: i32) -> int {
        if x % 2 == 0 { x as int } else { 0 }
    }

    pub open spec fn sum_even_prefix(nums: Seq<i32>, n: int) -> int
        decreases n
    {
        if n <= 0 {
            0
        } else {
            Self::sum_even_prefix(nums, n - 1) + Self::even_contrib(nums[n - 1])
        }
    }

    pub open spec fn sum_even(nums: Seq<i32>) -> int {
        Self::sum_even_prefix(nums, nums.len() as int)
    }

    pub open spec fn apply_query(nums: Seq<i32>, query: Vec<i32>) -> Seq<i32>
        recommends
            query@.len() == 2,
            0 <= query@[1] < nums.len(),
    {
        nums.update(query@[1] as int, (nums[query@[1] as int] + query@[0]) as i32)
    }

    pub open spec fn state_after(nums0: Seq<i32>, queries: Seq<Vec<i32>>, t: int) -> Seq<i32>
        recommends
            0 <= t <= queries.len(),
            forall |i: int| 0 <= i < queries.len() ==>
                queries[i].len() == 2 && 0 <= #[trigger] queries[i][1] < nums0.len(),
        decreases t
    {
        if t <= 0 {
            nums0
        } else {
            Self::apply_query(Self::state_after(nums0, queries, t - 1), queries[t - 1])
        }
    }

    pub open spec fn answers_prefix(nums0: Seq<i32>, queries: Seq<Vec<i32>>, t: int) -> Seq<i32>
        recommends
            0 <= t <= queries.len(),
            forall |i: int| 0 <= i < queries.len() ==>
                queries[i].len() == 2 && 0 <= #[trigger] queries[i][1] < nums0.len(),
        decreases t
    {
        if t <= 0 {
            seq![]
        } else {
            let prev = Self::answers_prefix(nums0, queries, t - 1);
            prev.push(Self::sum_even(Self::state_after(nums0, queries, t)) as i32)
        }
    }

    pub fn sum_even_after_queries(nums: Vec<i32>, queries: Vec<Vec<i32>>) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 10_000,
            forall |i: int| 0 <= i < nums.len() ==> -10_000 <= #[trigger] nums[i] <= 10_000,
            1 <= queries.len() <= 10_000,
            forall |i: int| 0 <= i < queries.len() ==>
                queries[i].len() == 2
                && -10_000 <= queries[i][0] <= 10_000
                && 0 <= queries[i][1] < nums.len(),
        ensures
            result@ == Self::answers_prefix(nums@, queries@, queries.len() as int),
    {
        let mut nums = nums;
        let ghost nums0 = nums@;

        let mut even_sum: i128 = 0;
        let mut i: usize = 0;
        while i < nums.len()
            invariant
                nums@ == nums0,
                0 <= i <= nums.len(),
                even_sum as int == Self::sum_even_prefix(nums0, i as int),
                -(i as int) * 10_000 <= even_sum as int <= (i as int) * 10_000,
                1 <= nums.len() <= 10_000,
                forall |j: int| 0 <= j < nums.len() ==> -10_000 <= #[trigger] nums[j] <= 10_000,
            decreases nums.len() - i,
        {
            let ghost old_even_sum = even_sum as int;
            if nums[i] % 2 == 0 {
                even_sum = even_sum + nums[i] as i128;
            }
            proof {
                assert(nums[i as int] == nums0[i as int]);
                assert(Self::sum_even_prefix(nums0, (i + 1) as int)
                    == Self::sum_even_prefix(nums0, i as int) + Self::even_contrib(nums0[i as int]));
                if nums0[i as int] % 2 == 0 {
                    assert(Self::even_contrib(nums0[i as int]) == nums0[i as int] as int);
                    assert(even_sum as int == old_even_sum + nums0[i as int] as int);
                } else {
                    assert(Self::even_contrib(nums0[i as int]) == 0);
                    assert(even_sum as int == old_even_sum);
                }
                assert(-(i as int + 1) * 10_000 <= even_sum as int <= (i as int + 1) * 10_000) by(nonlinear_arith)
                    requires
                        -(i as int) * 10_000 <= old_even_sum <= (i as int) * 10_000,
                        -10_000 <= nums0[i as int] as int <= 10_000,
                        even_sum as int == old_even_sum || even_sum as int == old_even_sum + nums0[i as int] as int
                {}
            }
            i = i + 1;
        }

        let mut result: Vec<i32> = Vec::new();
        let mut q: usize = 0;
        while q < queries.len()
            invariant
                nums@ == Self::state_after(nums0, queries@, q as int),
                result@ == Self::answers_prefix(nums0, queries@, q as int),
                even_sum as int == Self::sum_even(nums@),
                0 <= q <= queries.len(),
                nums.len() == nums0.len(),
                1 <= nums0.len() <= 10_000,
                1 <= queries.len() <= 10_000,
                forall |i2: int| 0 <= i2 < nums0.len() ==> -10_000 <= #[trigger] nums0[i2] <= 10_000,
                forall |i2: int| 0 <= i2 < queries.len() ==>
                    queries[i2].len() == 2
                    && -10_000 <= queries[i2][0] <= 10_000
                    && 0 <= queries[i2][1] < nums0.len(),
            decreases queries.len() - q,
        {
            let val = queries[q][0];
            let idx = queries[q][1] as usize;

            proof {
                assert(queries[q as int].len() == 2);
                assert(0 <= queries[q as int][1] < nums.len());
            }

            let old = nums[idx];
            let new_val_i64 = old as i64 + val as i64;
            let new_val = new_val_i64 as i32;
            nums.set(idx, new_val);

            even_sum = 0;
            let mut p: usize = 0;
            while p < nums.len()
                invariant
                    nums@ == Self::apply_query(Self::state_after(nums0, queries@, q as int), queries[q as int]),
                    0 <= p <= nums.len(),
                    1 <= nums.len() <= 10_000,
                    even_sum as int == Self::sum_even_prefix(nums@, p as int),
                    -(p as int) * 2_147_483_648 <= even_sum as int <= (p as int) * 2_147_483_648,
                decreases nums.len() - p,
            {
                let ghost old_even_sum = even_sum as int;
                if nums[p] % 2 == 0 {
                    proof {
                        assert(-2_147_483_648 <= nums[p as int] as int <= 2_147_483_647);
                        assert(-((p as int) + 1) * 2_147_483_648 <= old_even_sum + nums[p as int] as int) by(nonlinear_arith)
                            requires
                                -(p as int) * 2_147_483_648 <= old_even_sum,
                                -2_147_483_648 <= nums[p as int] as int
                        {}
                        assert(old_even_sum + nums[p as int] as int <= ((p as int) + 1) * 2_147_483_648) by(nonlinear_arith)
                            requires
                                old_even_sum <= (p as int) * 2_147_483_648,
                                nums[p as int] as int <= 2_147_483_647
                        {}
                        assert(((p as int) + 1) * 2_147_483_648 <= 21_476_311_279_648) by(nonlinear_arith)
                            requires p < nums.len(), nums.len() <= 10_000
                        {}
                        assert(-21_476_311_279_648 <= -((p as int) + 1) * 2_147_483_648) by(nonlinear_arith)
                            requires p < nums.len(), nums.len() <= 10_000
                        {}
                    }
                    even_sum = even_sum + nums[p] as i128;
                }
                proof {
                    assert(Self::sum_even_prefix(nums@, (p + 1) as int)
                        == Self::sum_even_prefix(nums@, p as int) + Self::even_contrib(nums@[p as int]));
                    if nums[p as int] % 2 == 0 {
                        assert(Self::even_contrib(nums@[p as int]) == nums[p as int] as int);
                        assert(even_sum as int == old_even_sum + nums[p as int] as int);
                    } else {
                        assert(Self::even_contrib(nums@[p as int]) == 0);
                        assert(even_sum as int == old_even_sum);
                    }
                    assert(-(p as int + 1) * 2_147_483_648 <= even_sum as int <= (p as int + 1) * 2_147_483_648) by {
                        if nums[p as int] % 2 == 0 {
                            assert(-(p as int + 1) * 2_147_483_648 <= old_even_sum + nums[p as int] as int) by(nonlinear_arith)
                                requires
                                    -(p as int) * 2_147_483_648 <= old_even_sum,
                                    -2_147_483_648 <= nums[p as int] as int
                            {}
                            assert(old_even_sum + nums[p as int] as int <= (p as int + 1) * 2_147_483_648) by(nonlinear_arith)
                                requires
                                    old_even_sum <= (p as int) * 2_147_483_648,
                                    nums[p as int] as int <= 2_147_483_647
                            {}
                        } else {
                            assert(-(p as int + 1) * 2_147_483_648 <= old_even_sum <= (p as int + 1) * 2_147_483_648) by(nonlinear_arith)
                                requires
                                    -(p as int) * 2_147_483_648 <= old_even_sum <= (p as int) * 2_147_483_648
                            {}
                        }
                    }
                }
                p = p + 1;
            }

            result.push(even_sum as i32);
            proof {
                assert(nums@ == Self::apply_query(Self::state_after(nums0, queries@, q as int), queries[q as int]));
                assert(result@ == Self::answers_prefix(nums0, queries@, q as int).push(even_sum as i32));
                assert(Self::state_after(nums0, queries@, q as int + 1)
                    == Self::apply_query(Self::state_after(nums0, queries@, q as int), queries[q as int]));
                assert(nums@ == Self::state_after(nums0, queries@, q as int + 1));
                assert(Self::answers_prefix(nums0, queries@, q as int + 1)
                    == Self::answers_prefix(nums0, queries@, q as int)
                        .push(Self::sum_even(Self::state_after(nums0, queries@, q as int + 1)) as i32));
                assert(even_sum as int == Self::sum_even(nums@));
            }
            q = q + 1;
        }

        result
    }
}

}
