use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn digit_sum(n: int) -> int
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            (n % 10) + Self::digit_sum(n / 10)
        }
    }

    pub open spec fn array_element_sum(nums: Seq<i32>, idx: int) -> int
        decreases idx,
    {
        if idx <= 0 {
            0
        } else {
            Self::array_element_sum(nums, idx - 1) + nums[idx - 1] as int
        }
    }

    pub open spec fn array_digit_sum(nums: Seq<i32>, idx: int) -> int
        decreases idx,
    {
        if idx <= 0 {
            0
        } else {
            Self::array_digit_sum(nums, idx - 1) + Self::digit_sum(nums[idx - 1] as int)
        }
    }

    pub open spec fn abs_diff(a: int, b: int) -> int {
        if a > b { a - b } else { b - a }
    }

    pub fn difference_of_sum(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 2000,
            forall|j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 2000,
        ensures
            result == Self::abs_diff(
                Self::array_element_sum(nums@, nums.len() as int), 
                Self::array_digit_sum(nums@, nums.len() as int)
            ),
    {
        let mut elem_sum: i32 = 0;
        let mut digit_sum: i32 = 0;
        let mut i: usize = 0;
        let n: usize = nums.len();

        while i < n 
            invariant
                1 <= n <= 2000,
                n == nums.len(),
                0 <= i <= n,
                0 <= elem_sum <= i * 2000,
                0 <= digit_sum <= i * 2000, 
                forall|j: int| 0 <= j < n ==> 1 <= #[trigger] nums[j] <= 2000,
                elem_sum as int == Self::array_element_sum(nums@, i as int),
                digit_sum as int == Self::array_digit_sum(nums@, i as int),
            decreases n - i,
        {
            let mut val = nums[i];
            elem_sum += val;

            let mut internal_digit_sum: i32 = 0;
            
            while val > 0
                invariant
                    0 <= i < nums.len(),
                    1 <= nums[i as int] <= 2000,
                    0 <= val <= nums[i as int],
                    0 <= internal_digit_sum,
                    internal_digit_sum + val <= nums[i as int],
                    internal_digit_sum as int + Self::digit_sum(val as int) == Self::digit_sum(nums[i as int] as int),
                decreases val,
            {
                let d = (val as u32 % 10) as i32;
                internal_digit_sum += d;
                val = (val as u32 / 10) as i32;
                
                proof {
                    
                }
            }
            
            digit_sum += internal_digit_sum;
            i += 1;
        }

        if elem_sum > digit_sum {
            elem_sum - digit_sum
        } else {
            digit_sum - elem_sum
        }
    }
}

}
