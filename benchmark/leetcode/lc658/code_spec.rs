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

    #[verifier::exec_allows_no_decreases_clause]
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
                && (start == 0 || !Self::closer(arr[start - 1], arr[start + k as int - 1], x))
                && (start + k as int >= arr.len() as int || !Self::closer(arr[start + k as int], arr[start], x)),
    {
        let n = arr.len();
        let k_usize = k as usize;
        if x <= arr[0] {
            let mut res = Vec::new();
            let mut i: usize = 0;
            while i < k_usize {
                res.push(arr[i]);
                i += 1;
            }
            res
        } else if x >= arr[n - 1] {
            let mut res = Vec::new();
            let start = n - k_usize;
            let mut i = start;
            while i < n {
                res.push(arr[i]);
                i += 1;
            }
            res
        } else {
            let mut low: usize = 0;
            let mut high = n - k_usize;
            while low < high {
                let mid = low + (high - low) / 2;
                let left_dist = x as i64 - arr[mid] as i64;
                let right_dist = arr[mid + k_usize] as i64 - x as i64;
                if left_dist > right_dist {
                    low = mid + 1;
                } else {
                    high = mid;
                }
            }
            let mut res = Vec::new();
            let mut i = low;
            while i < low + k_usize {
                res.push(arr[i]);
                i += 1;
            }
            res
        }
    }
}

}
