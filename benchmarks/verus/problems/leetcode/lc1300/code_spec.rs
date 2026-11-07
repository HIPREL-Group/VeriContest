use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn min_spec(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

pub open spec fn mutated_sum(arr: Seq<i32>, value: int) -> int
    decreases arr.len()
{
    if arr.len() == 0 {
        0
    } else {
        min_spec(arr[arr.len() - 1] as int, value) + mutated_sum(arr.drop_last(), value)
    }
}

pub open spec fn abs_diff(a: int, b: int) -> int {
    if a >= b { a - b } else { b - a }
}

fn compute_sum(arr: &Vec<i32>, value: i32) -> (result: i32)
    requires
        1 <= arr.len() <= 10_000,
        forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 100_000,
        0 <= value <= 100_000,
    ensures
        result as int == mutated_sum(arr@, value as int),
{
    let n = arr.len();
    let mut sum: i32 = 0;
    let mut j: usize = 0;
    while j < n {
        if arr[j] <= value {
            sum = sum + arr[j];
        } else {
            sum = sum + value;
        }
        j = j + 1;
    }
    sum
}

impl Solution {
    pub fn find_best_value(arr: Vec<i32>, target: i32) -> (result: i32)
        requires
            1 <= arr.len() <= 10_000,
            forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 100_000,
            1 <= target <= 100_000,
        ensures
            result >= 0,
            forall |v: int| #![trigger mutated_sum(arr@, v)] v >= 0 ==> abs_diff(mutated_sum(arr@, result as int), target as int) <= abs_diff(mutated_sum(arr@, v), target as int),
            forall |v: int| #![trigger mutated_sum(arr@, v)] (v >= 0 && abs_diff(mutated_sum(arr@, v), target as int) == abs_diff(mutated_sum(arr@, result as int), target as int)) ==> result as int <= v,
    {
        let n = arr.len();
        let mut max_val: i32 = arr[0];
        let mut i: usize = 1;
        while i < n {
            if arr[i] > max_val {
                max_val = arr[i];
            }
            i = i + 1;
        }
        let total_sum = compute_sum(&arr, max_val);
        if total_sum <= target {
            return max_val;
        }
        let mut lo: i32 = 0;
        let mut hi: i32 = max_val;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            let sum_mid = compute_sum(&arr, mid);
            if sum_mid >= target {
                hi = mid;
            } else {
                lo = mid + 1;
            }
        }
        let sum_lo = compute_sum(&arr, lo);
        let sum_prev = compute_sum(&arr, lo - 1);
        if sum_lo - target < target - sum_prev {
            lo
        } else {
            lo - 1
        }
    }
}

}
