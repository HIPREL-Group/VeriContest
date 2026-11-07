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
        let n = arr.len();
        let k_usize = k as usize;
        let mut low: usize = 0;
        let mut high = n - k_usize;
        while low < high
            invariant
                n == arr.len(),
                k_usize == k as usize,
                1 <= k as int <= n as int,
                0 <= low <= high <= n - k_usize,
                low == 0 || Self::should_move_right(arr@, low as int - 1, k as int, x as int),
                high + k_usize >= n || !Self::should_move_right(arr@, high as int, k as int, x as int),
            decreases high - low
        {
            let mid = low + (high - low) / 2;
            proof {
                assert(low <= mid);
                assert(mid < high);
                assert(high - (mid + 1) < high - low);
                assert(mid - low < high - low);
            }
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
        while i < low + k_usize
            invariant
                n == arr.len(),
                k_usize == k as usize,
                1 <= k as int <= n as int,
                0 <= low <= n - k_usize,
                low <= i <= low + k_usize,
                res.len() == i - low,
                res@ =~= arr@.subrange(low as int, i as int),
            decreases (low + k_usize) - i
        {
            res.push(arr[i]);
            i += 1;
        }
        proof {
            assert(res@ =~= arr@.subrange(low as int, (low + k_usize) as int));
            assert(res.len() == k as int);
            assert(forall|idx: int| 0 <= idx < k as int ==> res[idx] == arr[low as int + idx]);
            assert(0 <= low as int <= arr.len() - k as int);
            assert(forall|i: int| 0 <= i < k as int ==> res[i] == arr[low as int + i]);
            assert(arr[low as int + 0] == arr[low as int]);
        }
        res
    }
}

}
