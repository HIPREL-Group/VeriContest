use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn window_sum(nums: Seq<i32>, start: int, k: int) -> int
        decreases k
    {
        if k <= 0 {
            0
        } else {
            Self::window_sum(nums, start, k - 1) + nums[start + k - 1] as int
        }
    }

    pub open spec fn count_valid_windows(nums: Seq<i32>, k: int, threshold: int, n: int) -> int
        decreases n
    {
        if n <= 0 || n < k {
            0
        } else {
            Self::count_valid_windows(nums, k, threshold, n - 1)
                + if Self::window_sum(nums, n - k, k) >= threshold * k { 1int } else { 0int }
        }
    }

    pub fn num_of_subarrays(arr: Vec<i32>, k: i32, threshold: i32) -> (res: i32)
        requires
            1 <= arr.len(),
            arr.len() <= 100_000,
            1 <= k,
            k as usize <= arr.len(),
            forall |i: int| 0 <= i < arr.len() ==> 0 <= #[trigger] arr[i] <= 10_000,
            0 <= threshold,
            threshold <= 10_000,
        ensures
            res as int == Self::count_valid_windows(arr@, k as int, threshold as int, arr.len() as int),
    {
        let n = arr.len();
        let k_usize = k as usize;
        let mut sum = 0i64;
        let mut i = 0usize;
        while i < k_usize {
            sum += arr[i] as i64;
            i += 1;
        }
        let tk: i64 = threshold as i64 * k as i64;
        let mut count = 0i32;
        if sum >= tk {
            count += 1;
        }
        let mut i = k_usize;
        while i < n {
            sum += arr[i] as i64;
            sum -= arr[i - k_usize] as i64;
            if sum >= tk {
                count += 1;
            }
            i += 1;
        }
        count
    }
}

}
