use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn prefix_sum(arr: Seq<i32>, end: int) -> int
        recommends
            0 <= end <= arr.len(),
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::prefix_sum(arr, end - 1) + arr[end - 1] as int
        }
    }

    pub open spec fn total_sum(arr: Seq<i32>) -> int {
        Self::prefix_sum(arr, arr.len() as int)
    }

    pub open spec fn valid_partition(arr: Seq<i32>, a: int, b: int) -> bool {
        &&& 1 <= a < b < arr.len()
        &&& {
            let s1 = Self::prefix_sum(arr, a);
            let s2 = Self::prefix_sum(arr, b) - Self::prefix_sum(arr, a);
            let s3 = Self::total_sum(arr) - Self::prefix_sum(arr, b);
            s1 == s2 && s2 == s3
        }
    }

    pub fn can_three_parts_equal_sum(arr: Vec<i32>) -> (result: bool)
        requires
            3 <= arr.len() <= 50_000,
            forall |i: int| 0 <= i < arr.len() ==> -10_000 <= #[trigger] arr[i] <= 10_000,
        ensures
            result == (exists |a: int, b: int| Self::valid_partition(arr@, a, b)),
    {
        let n = arr.len();
        let mut total: i128 = 0;
        let mut i: usize = 0;
        while i < n {
            total = total + arr[i] as i128;
            i += 1;
        }

        let target = total / 3;
        if target * 3 != total {
            return false;
        }

        let mut prefix: i128 = 0;
        i = 0;
        while i < n - 2 {
            let next_prefix = prefix + arr[i] as i128;
            prefix = next_prefix;
            if prefix == target {
                let first_end = i + 1;
                i += 1;
                while i < n - 1 {
                    let next_prefix = prefix + arr[i] as i128;
                    prefix = next_prefix;
                    if prefix == 2 * target {
                        return true;
                    }
                    i += 1;
                }
                return false;
            }
            i += 1;
        }

        false
    }
}

}
