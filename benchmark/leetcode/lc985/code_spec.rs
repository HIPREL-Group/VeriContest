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
        let mut even_sum: i128 = 0;
        let mut i: usize = 0;
        while i < nums.len()
        {
            if nums[i] % 2 == 0 {
                even_sum = even_sum + nums[i] as i128;
            }
            i = i + 1;
        }

        let mut result: Vec<i32> = Vec::new();
        let mut q: usize = 0;
        while q < queries.len()
        {
            let val = queries[q][0];
            let idx = queries[q][1] as usize;

            let old = nums[idx];
            let new_val_i64 = old as i64 + val as i64;
            let new_val = new_val_i64 as i32;
            nums.set(idx, new_val);

            even_sum = 0;
            let mut p: usize = 0;
            while p < nums.len()
            {
                if nums[p] % 2 == 0 {
                    even_sum = even_sum + nums[p] as i128;
                }
                p = p + 1;
            }

            result.push(even_sum as i32);
            q = q + 1;
        }

        result
    }
}

}
