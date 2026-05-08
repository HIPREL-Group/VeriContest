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

        while start < n {
            let mut sum: i32 = 0;
            let mut end: usize = start;
            let total_before_start: i64 = total;

            while end < n {
                sum += arr[end];

                let len = end - start + 1;

                if len % 2 == 1 {
                    total += sum as i64;
                }

                end += 1;
            }

            start += 1;
        }
        total as i32
    }
}

}
