use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn subarray_sum(arr: Seq<i32>, start: int, end: int) -> int
        decreases end - start,
    {
        if start >= end { 0 }
        else { arr[start] as int + Self::subarray_sum(arr, start + 1, end) }
    }

    pub open spec fn inner_sum(arr: Seq<i32>, start: int, end: int) -> int
        decreases arr.len() - end,
    {
        if end >= arr.len() { 0 }
        else {
            (if (end - start + 1) % 2 == 1 { Self::subarray_sum(arr, start, end + 1) } else { 0int }) +
            Self::inner_sum(arr, start, end + 1)
        }
    }

    pub open spec fn outer_sum(arr: Seq<i32>, start: int) -> int
        decreases arr.len() - start,
    {
        if start >= arr.len() { 0 }
        else {
            Self::inner_sum(arr, start, start) +
            Self::outer_sum(arr, start + 1)
        }
    }

    proof fn subarray_sum_extend(arr: Seq<i32>, start: int, end: int)
        requires 0 <= start <= end, end < arr.len(),
        ensures Self::subarray_sum(arr, start, end + 1) ==
            Self::subarray_sum(arr, start, end) + arr[end] as int,
        decreases end - start,
    {
        reveal_with_fuel(Solution::subarray_sum, 2);
        if start < end {
            Self::subarray_sum_extend(arr, start + 1, end);
        }
    }

    proof fn subarray_sum_nonneg(arr: Seq<i32>, start: int, end: int)
        requires 0 <= start, end <= arr.len(),
            forall |i: int| 0 <= i < arr.len() ==> 0 <= #[trigger] arr[i],
        ensures Self::subarray_sum(arr, start, end) >= 0,
        decreases end - start,
    {
        if start < end {
            Self::subarray_sum_nonneg(arr, start + 1, end);
        }
    }

    proof fn inner_sum_nonneg(arr: Seq<i32>, start: int, end: int)
        requires 0 <= start, end >= start,
            forall |i: int| 0 <= i < arr.len() ==> 0 <= #[trigger] arr[i] <= 1000,
        ensures Self::inner_sum(arr, start, end) >= 0,
        decreases arr.len() - end,
    {
        if end < arr.len() {
            Self::inner_sum_nonneg(arr, start, end + 1);
            Self::subarray_sum_nonneg(arr, start, end + 1);
        }
    }

    proof fn outer_sum_nonneg(arr: Seq<i32>, start: int)
        requires 0 <= start,
            forall |i: int| 0 <= i < arr.len() ==> 0 <= #[trigger] arr[i] <= 1000,
        ensures Self::outer_sum(arr, start) >= 0,
        decreases arr.len() - start,
    {
        if start < arr.len() {
            Self::inner_sum_nonneg(arr, start, start);
            Self::outer_sum_nonneg(arr, start + 1);
        }
    }

    pub fn sum_odd_length_subarrays(arr: Vec<i32>) -> (result: i32)
        requires
            1 <= arr.len() <= 100,
            forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 1000,
        ensures
            result as int == Self::outer_sum(arr@, 0),
    {
        let n = arr.len();
        let mut total: i64 = 0;
        let mut start: usize = 0;

        while start < n
            invariant
                n == arr.len(),
                1 <= n <= 100,
                0 <= start <= n,
                forall |i: int| 0 <= i < n as int ==> 1 <= #[trigger] arr[i] <= 1000,
                total as int == Self::outer_sum(arr@, 0) - Self::outer_sum(arr@, start as int),
                total <= start as i64 * 10_000_000i64,
                0 <= total,
            decreases n - start,
        {
            let mut sum: i32 = 0;
            let mut end: usize = start;
            let total_before_start: i64 = total;

            while end < n
                invariant
                    n == arr.len(),
                    1 <= n <= 100,
                    0 <= start < n,
                    start <= end <= n,
                    forall |i: int| 0 <= i < n as int ==> 1 <= #[trigger] arr[i] <= 1000,
                    sum as int == Self::subarray_sum(arr@, start as int, end as int),
                    0 <= sum,
                    sum <= (end - start) as i32 * 1000,
                    total_before_start as int == Self::outer_sum(arr@, 0) - Self::outer_sum(arr@, start as int),
                    0 <= total_before_start,
                    total_before_start <= start as i64 * 10_000_000i64,
                    total as int == total_before_start as int
                        + Self::inner_sum(arr@, start as int, start as int)
                        - Self::inner_sum(arr@, start as int, end as int),
                    total <= total_before_start + (end - start) as i64 * 100_000i64,
                    0 <= total,
                decreases n - end,
            {
                proof {
                    Self::subarray_sum_extend(arr@, start as int, end as int);
                    Self::inner_sum_nonneg(arr@, start as int, (end + 1) as int);
                }

                assert(sum <= (end - start) as i32 * 1000);
                assert((end - start) <= 99);
                assert((end - start) as i32 * 1000 <= 99_000);
                sum += arr[end];

                let len = end - start + 1;

                proof {
                    assert((len as int) % 2 == ((end as int - start as int + 1) % 2));
                    assert(Self::inner_sum(arr@, start as int, end as int) ==
                        (if ((end as int - start as int + 1) % 2 == 1) { Self::subarray_sum(arr@, start as int, (end + 1) as int) } else { 0int }) +
                        Self::inner_sum(arr@, start as int, (end + 1) as int));
                }

                if len % 2 == 1 {
                    assert(sum <= len as i32 * 1000);
                    assert(len <= 100);
                    assert(sum <= 100_000);
                    total += sum as i64;
                }

                end += 1;
            }

            proof {
                Self::outer_sum_nonneg(arr@, (start + 1) as int);
            }

            start += 1;
        }
        total as i32
    }
}

}
