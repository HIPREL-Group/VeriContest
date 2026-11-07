use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_mountain_triplet(nums: Seq<i32>, i: int, j: int, k: int) -> bool {
        &&& 0 <= i < j < k < nums.len()
        &&& nums[i] < nums[j]
        &&& nums[k] < nums[j]
    }

    pub open spec fn triplet_sum(nums: Seq<i32>, i: int, j: int, k: int) -> int {
        nums[i] as int + nums[j] as int + nums[k] as int
    }

    pub fn minimum_sum(nums: Vec<i32>) -> (result: i32)
        requires
            3 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100000000,
        ensures
            result == -1 ==> forall |i: int, j: int, k: int|
                !Self::is_mountain_triplet(nums@, i, j, k),
            result != -1 ==> exists |i: int, j: int, k: int|
                Self::is_mountain_triplet(nums@, i, j, k)
                && result as int == Self::triplet_sum(nums@, i, j, k),
            result != -1 ==> forall |i: int, j: int, k: int|
                Self::is_mountain_triplet(nums@, i, j, k)
                ==> result as int <= Self::triplet_sum(nums@, i, j, k),
    {
        let n = nums.len();

        let mut left_idx: Vec<usize> = Vec::new();
        left_idx.push(0);
        let mut p: usize = 1;
        while p < n {
            let mut best = left_idx[p - 1];
            if nums[p] < nums[best] {
                best = p;
            }
            left_idx.push(best);
            p += 1;
        }

        let mut right_idx: Vec<usize> = Vec::new();
        let mut q: usize = 0;
        while q < n {
            right_idx.push(q);
            q += 1;
        }

        let mut q: usize = n - 1;
        while q > 0 {
            let prev = q - 1;
            let mut best = right_idx[q];
            if nums[prev] <= nums[best] {
                best = prev;
            }
            right_idx.set(prev, best);
            q -= 1;
        }

        let mut best_sum: i32 = 300000001;
        let mut j: usize = 1;
        while j + 1 < n {
            let left = left_idx[j - 1];
            let right = right_idx[j + 1];
            if nums[left] < nums[j] && nums[right] < nums[j] {
                let candidate = nums[left] + nums[j] + nums[right];
                if candidate < best_sum {
                    best_sum = candidate;
                }
            }
            j += 1;
        }

        if best_sum == 300000001 {
            -1
        } else {
            best_sum
        }
    }
}

}
