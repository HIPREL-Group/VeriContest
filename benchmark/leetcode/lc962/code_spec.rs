use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_suffix_max_at(nums: Seq<i32>, rm: Seq<i32>, j: int) -> bool {
    0 <= j < nums.len()
    && rm[j] >= nums[j]
    && (forall |k: int| j <= k < nums.len() ==> nums[k] <= rm[j])
    && (exists |k: int| j <= k < nums.len() && nums[k] == rm[j])
}

impl Solution {
    pub fn max_width_ramp(nums: Vec<i32>) -> (result: i32)
        requires
            2 <= nums.len() <= 50_000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 50_000,
        ensures
            0 <= result <= nums.len() as int - 1,
            forall |i: int, j: int|
                0 <= i < j < nums.len() && nums[i] <= nums[j] ==> j - i <= result,
            result == 0 <==> (forall |i: int, j: int|
                0 <= i < j < nums.len() ==> nums[i] > nums[j]),
            result > 0 ==> (exists |i: int, j: int|
                0 <= i < j < nums.len() && nums[i] <= nums[j] && result == j - i),
    {
        let n = nums.len();

        let mut right_max: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
        {
            right_max.push(0i32);
            k += 1;
        }

        right_max[n - 1] = nums[n - 1];

        if n >= 2 {
            let mut k: usize = n - 1;
            while k > 0
            {
                k -= 1;
                if nums[k] > right_max[k + 1] {
                    right_max[k] = nums[k];
                } else {
                    right_max[k] = right_max[k + 1];
                }
            }
        }

        let mut best: i32 = 0;
        let mut i: usize = 0;
        let mut j: usize = 0;

        while j < n
        {
            if nums[i] <= right_max[j] {
                let width = (j - i) as i32;
                if width > best {
                    best = width;
                }
                j += 1;
            } else {
                i += 1;
                if i > j {
                    j = i;
                }
            }
        }

        best
    }
}

}
