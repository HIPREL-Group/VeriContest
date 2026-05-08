use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn best_in_prefix(nums: Seq<i32>, marked: Seq<bool>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            nums.len() as int
        } else {
            let prev = Self::best_in_prefix(nums, marked, end - 1);
            let j = end - 1;
            if marked[j] {
                prev
            } else if prev == nums.len() as int || nums[j] < nums[prev] || (nums[j] == nums[prev] && j < prev) {
                j
            } else {
                prev
            }
        }
    }

    pub open spec fn best_unmarked(nums: Seq<i32>, marked: Seq<bool>) -> int {
        Self::best_in_prefix(nums, marked, nums.len() as int)
    }

    pub open spec fn sum_unmarked_prefix(nums: Seq<i32>, marked: Seq<bool>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::sum_unmarked_prefix(nums, marked, end - 1)
                + if marked[end - 1] { 0 } else { nums[end - 1] as int }
        }
    }

    pub open spec fn sum_unmarked(nums: Seq<i32>, marked: Seq<bool>) -> int {
        Self::sum_unmarked_prefix(nums, marked, nums.len() as int)
    }

    pub open spec fn all_unmarked(n: int) -> Seq<bool>
        decreases n,
    {
        if n <= 0 {
            seq![]
        } else {
            Self::all_unmarked(n - 1).push(false)
        }
    }

    pub open spec fn mark_index(marked: Seq<bool>, idx: int) -> Seq<bool> {
        if marked[idx] {
            marked
        } else {
            marked.update(idx, true)
        }
    }

    pub open spec fn mark_steps(nums: Seq<i32>, marked: Seq<bool>, steps: int) -> Seq<bool>
        decreases steps,
    {
        if steps <= 0 {
            marked
        } else {
            let prev = Self::mark_steps(nums, marked, steps - 1);
            let b = Self::best_unmarked(nums, prev);
            if b == nums.len() as int {
                prev
            } else {
                prev.update(b, true)
            }
        }
    }

    pub open spec fn apply_query(nums: Seq<i32>, marked: Seq<bool>, query: Vec<i32>) -> Seq<bool> {
        let marked1 = Self::mark_index(marked, query[0] as int);
        Self::mark_steps(nums, marked1, query[1] as int)
    }

    pub open spec fn state_after(nums: Seq<i32>, queries: Seq<Vec<i32>>, t: int) -> Seq<bool>
        decreases t,
    {
        if t <= 0 {
            Self::all_unmarked(nums.len() as int)
        } else {
            let prev = Self::state_after(nums, queries, t - 1);
            Self::apply_query(nums, prev, queries[t - 1])
        }
    }

    pub open spec fn answers_prefix(nums: Seq<i32>, queries: Seq<Vec<i32>>, t: int) -> Seq<i64>
        decreases t,
    {
        if t <= 0 {
            seq![]
        } else {
            let prev = Self::answers_prefix(nums, queries, t - 1);
            let marks = Self::state_after(nums, queries, t);
            prev.push(Self::sum_unmarked(nums, marks) as i64)
        }
    }

    pub fn unmarked_sum_array(nums: Vec<i32>, queries: Vec<Vec<i32>>) -> (result: Vec<i64>)
        requires
            1 <= queries.len() <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100_000,
            forall |i: int| 0 <= i < queries.len() ==> #[trigger] queries[i].len() == 2,
            forall |i: int| 0 <= i < queries.len() && queries[i].len() == 2 ==> 0 <= #[trigger] queries[i][0] < nums.len(),
            forall |i: int| 0 <= i < queries.len() && queries[i].len() == 2 ==> 0 <= #[trigger] queries[i][1] <= nums.len() - 1,
        ensures
            result@ == Self::answers_prefix(nums@, queries@, queries.len() as int),
    {
        let n = nums.len();

        let mut marked: Vec<bool> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            marked.push(false);
            i = i + 1;
        }

        let mut result: Vec<i64> = Vec::new();
        let mut q: usize = 0;
        while q < queries.len() {
            let idx_i32 = queries[q][0];
            let k = queries[q][1];
            let idx = idx_i32 as usize;

            if !marked[idx] {
                marked.set(idx, true);
            }

            let mut t: i32 = 0;
            while t < k {
                let mut best: usize = n;
                let mut j: usize = 0;
                while j < n {
                    if !marked[j] {
                        if best == n {
                            best = j;
                        } else if nums[j] < nums[best] || (nums[j] == nums[best] && j < best) {
                            best = j;
                        }
                    }
                    j = j + 1;
                }
                if best < n {
                    marked.set(best, true);
                }
                t = t + 1;
            }

            let mut unmarked_sum: i128 = 0;
            let mut p: usize = 0;
            while p < n {
                if !marked[p] {
                    unmarked_sum = unmarked_sum + nums[p] as i128;
                }
                p = p + 1;
            }

            result.push(unmarked_sum as i64);
            q = q + 1;
        }

        result
    }
}

}
