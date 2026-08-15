use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn closer(a: i32, b: i32, x: i32) -> bool {
        let da = if a >= x { a - x } else { x - a };
        let db = if b >= x { b - x } else { x - b };
        da < db || (da == db && a < b)
    }

    pub open spec fn should_move_right(arr: Seq<i32>, s: int, k: int, x: int) -> bool {
        x - arr[s] as int > arr[s + k] as int - x
    }

    pub fn find_closest_elements(arr: Vec<i32>, k: i32, x: i32) -> (result: Vec<i32>)
        requires
            1 <= k <= arr.len() as i32,
            1 <= arr.len() <= 10000,
            forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
            forall|i: int| 0 <= i < arr.len() ==> -10000 <= #[trigger] arr[i] <= 10000,
            -10000 <= x <= 10000,
        ensures
            result.len() == k as int,
            forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
            forall|i: int| 0 <= i < result.len() ==>
                exists|j: int| 0 <= j < arr.len() && #[trigger] result[i] == arr[j],
            exists|start: int| #![trigger arr[start + 0]]
                0 <= start <= arr.len() - k as int
                && forall|i: int| 0 <= i < k as int ==> result[i] == arr[start + i]
                && (start == 0 || Self::should_move_right(arr@, start - 1, k as int, x as int))
                && (start + k as int >= arr.len() as int || !Self::should_move_right(arr@, start, k as int, x as int)),
    {
    }
}

}
