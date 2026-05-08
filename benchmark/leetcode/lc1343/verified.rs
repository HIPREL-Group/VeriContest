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

    proof fn lemma_window_slide(arr: Seq<i32>, start: int, k: int)
        requires
            0 <= start,
            0 < k,
            start + k < arr.len(),
        ensures
            Self::window_sum(arr, start + 1, k) ==
                Self::window_sum(arr, start, k) + arr[start + k] as int - arr[start] as int,
        decreases k
    {
        reveal_with_fuel(Solution::window_sum, 2);
        if k > 1 {
            Self::lemma_window_slide(arr, start, k - 1);
        }
    }

    proof fn lemma_window_sum_upper(arr: Seq<i32>, start: int, k: int)
        requires
            0 <= start,
            0 <= k,
            start + k <= arr.len(),
            forall |i: int| 0 <= i < arr.len() ==> #[trigger] arr[i] <= 10_000,
        ensures
            Self::window_sum(arr, start, k) <= k * 10_000,
        decreases k
    {
        if k > 0 {
            Self::lemma_window_sum_upper(arr, start, k - 1);
        }
    }

    proof fn lemma_window_sum_nonneg(arr: Seq<i32>, start: int, k: int)
        requires
            0 <= start,
            0 <= k,
            start + k <= arr.len(),
            forall |i: int| 0 <= i < arr.len() ==> 0 <= #[trigger] arr[i],
        ensures
            0 <= Self::window_sum(arr, start, k),
        decreases k
    {
        if k > 0 {
            Self::lemma_window_sum_nonneg(arr, start, k - 1);
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
        while i < k_usize
            invariant
                i <= k_usize,
                k_usize == k as usize,
                k_usize <= n,
                n == arr.len(),
                n <= 100_000,
                sum as int == Self::window_sum(arr@, 0int, i as int),
                0 <= sum as int,
                sum as int <= i as int * 10_000,
                forall |j: int| 0 <= j < arr.len() ==> 0 <= #[trigger] arr[j] <= 10_000,
            decreases k_usize - i
        {
            proof {
                assert(sum as int + arr@[i as int] as int <= i as int * 10_000 + 10_000) by (nonlinear_arith)
                    requires
                        sum as int <= i as int * 10_000,
                        arr@[i as int] as int <= 10_000,
                {};
            }
            sum += arr[i] as i64;
            i += 1;
        }

        proof {
            assert(threshold as int * k as int >= 0) by (nonlinear_arith)
                requires
                    0 <= threshold as int,
                    0 <= k as int,
            {};
            assert(threshold as int * k as int <= 10_000 * 100_000) by (nonlinear_arith)
                requires
                    0 <= threshold as int,
                    threshold as int <= 10_000,
                    0 < k as int,
                    k as int <= 100_000,
            {};
        }
        let tk: i64 = threshold as i64 * k as i64;

        let mut count = 0i32;
        if sum >= tk {
            count += 1;
        }

        proof {
            assert(Self::count_valid_windows(arr@, k as int, threshold as int, k_usize as int - 1) == 0int);
            assert(count as int == Self::count_valid_windows(arr@, k as int, threshold as int, k_usize as int));
        }

        let mut i = k_usize;
        while i < n
            invariant
                k_usize <= i,
                i <= n,
                k_usize as int == k as int,
                1 <= k_usize,
                n == arr.len(),
                1 <= arr.len(),
                arr.len() <= 100_000,
                tk as int == threshold as int * k as int,
                sum as int == Self::window_sum(arr@, (i - k_usize) as int, k as int),
                count as int == Self::count_valid_windows(arr@, k as int, threshold as int, i as int),
                0 <= sum as int,
                sum as int <= k as int * 10_000,
                0 <= count as int,
                count as int <= i as int,
                0 <= threshold as int,
                threshold as int <= 10_000,
                0 <= tk as int,
                tk as int <= 10_000 * 100_000,
                forall |j: int| 0 <= j < arr.len() ==> 0 <= #[trigger] arr[j] <= 10_000,
            decreases n - i
        {
            sum += arr[i] as i64;

            proof {
                Self::lemma_window_slide(arr@, (i - k_usize) as int, k as int);
            }
            
            sum -= arr[i - k_usize] as i64;

            proof {
                Self::lemma_window_sum_nonneg(arr@, (i - k_usize + 1) as int, k as int);
                Self::lemma_window_sum_upper(arr@, (i - k_usize + 1) as int, k as int);
            }

            if sum >= tk {
                count += 1;
            }

            proof {
                assert(count as int == Self::count_valid_windows(arr@, k as int, threshold as int, (i + 1) as int));
            }

            i += 1;
        }

        count
    }
}

}
