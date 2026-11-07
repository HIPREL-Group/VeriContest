use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn seen_after_prefix(nums: Seq<i32>, end: int) -> Seq<i32>
        decreases end,
    {
        if end <= 0 {
            Seq::<i32>::empty()
        } else {
            let prev = Self::seen_after_prefix(nums, end - 1);
            let x = nums[end - 1];
            if x == -1i32 { prev } else { prev.push(x) }
        }
    }

    pub open spec fn consecutive_minus_ones(nums: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            let x = nums[end - 1];
            if x == -1i32 {
                Self::consecutive_minus_ones(nums, end - 1) + 1
            } else {
                0
            }
        }
    }

    pub open spec fn ans_after_prefix(nums: Seq<i32>, end: int) -> Seq<i32>
        decreases end,
    {
        if end <= 0 {
            Seq::<i32>::empty()
        } else {
            let prev_ans = Self::ans_after_prefix(nums, end - 1);
            let prev_seen = Self::seen_after_prefix(nums, end - 1);
            let prev_k = Self::consecutive_minus_ones(nums, end - 1);
            let x = nums[end - 1];
            if x == -1i32 {
                let nk = prev_k + 1;
                if nk <= prev_seen.len() {
                    prev_ans.push(prev_seen[prev_seen.len() - nk])
                } else {
                    prev_ans.push(-1i32)
                }
            } else {
                prev_ans
            }
        }
    }

    pub open spec fn last_visited_spec(nums: Seq<i32>) -> Seq<i32> {
        Self::ans_after_prefix(nums, nums.len() as int)
    }

    pub fn last_visited_integers(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> nums[i] == -1i32 || (1 <= #[trigger] nums[i] <= 100),
        ensures
            result@ == Self::last_visited_spec(nums@),
    {
        let n = nums.len();
        let mut seen: Vec<i32> = Vec::new();
        let mut ans: Vec<i32> = Vec::new();
        let mut consecutive: usize = 0;
        let mut i: usize = 0;
        while i < n {
            let x = nums[i];
            if x == -1 {
                consecutive += 1;
                if consecutive <= seen.len() {
                    let idx = seen.len() - consecutive;
                    ans.push(seen[idx]);
                } else {
                    ans.push(-1);
                }
            } else {
                seen.push(x);
                consecutive = 0;
            }
            i += 1;
        }
        ans
    }
}

}
