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
            while i < k_usize
                invariant
                    n == arr.len(),
                    k_usize == k as usize,
                    1 <= k as int <= n as int,
                    0 <= i <= k_usize,
                    res.len() == i,
                    res@ =~= arr@.subrange(0, i as int),
                decreases k_usize - i
            {
                res.push(arr[i]);
                i += 1;
            }
            proof {
                assert(res@ =~= arr@.subrange(0, k as int));
                assert(res.len() == k as int);
                assert(forall|idx: int| 0 <= idx < k as int ==> res[idx] == arr[idx]);
                assert(0 <= 0 <= arr.len() - k as int);
                assert(forall|i: int| 0 <= i < k as int ==> res[i] == arr[0 + i]);
                assert(#[trigger] arr[(0 as int) + 0] == arr[0]);
                if k_usize < n {
                    let c = arr[k as int];
                    let d = arr[0];
                    assert(x <= d);
                    assert(d <= c);
                    assert(!Self::closer(c, d, x));
                }
            }
            res
        } else if x >= arr[n - 1] {
            let mut res = Vec::new();
            let start = n - k_usize;
            let mut i = start;
            while i < n
                invariant
                    n == arr.len(),
                    k_usize == k as usize,
                    1 <= k as int <= n as int,
                    start == n - k_usize,
                    start <= i <= n,
                    res.len() == i - start,
                    res@ =~= arr@.subrange(start as int, i as int),
                decreases n - i
            {
                res.push(arr[i]);
                i += 1;
            }
            proof {
                assert(res@ =~= arr@.subrange(start as int, n as int));
                assert(res.len() == k as int);
                assert(forall|idx: int| 0 <= idx < k as int ==> res[idx] == arr[start as int + idx]);
                assert(0 <= start as int <= arr.len() - k as int);
                assert(forall|i: int| 0 <= i < k as int ==> res[i] == arr[start as int + i]);
                assert(arr[start as int + 0] == arr[start as int]);
                if start > 0 {
                    let a = arr[start as int - 1];
                    let b = arr[(start + k_usize - 1) as int];
                    assert(a <= b);
                    assert(b <= x);
                    assert(!Self::closer(a, b, x));
                }
            }
            res
        } else {
            let mut low: usize = 0;
            let mut high = n - k_usize;
            while low < high
                invariant
                    n == arr.len(),
                    k_usize == k as usize,
                    1 <= k as int <= n as int,
                    0 <= low <= high <= n - k_usize,
                    low == 0 || (x as int - arr[low as int - 1] as int > arr[low as int - 1 + k as int] as int - x as int),
                    high + k_usize >= n || (arr[(high + k_usize) as int] as int - x as int >= x as int - arr[high as int] as int),
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
                if low > 0 {
                    let s = low as int;
                    let a = arr[s - 1];
                    let b = arr[s + k as int - 1];
                    assert(0 <= s - 1 < s + k as int - 1 < arr.len() as int);
                    assert(a <= b);
                    assert(x as int - a as int > b as int - x as int);
                    assert(!Self::closer(a, b, x));
                }
                if (low + k_usize) < n {
                    let s = low as int;
                    let c = arr[s + k as int];
                    let d = arr[s];
                    assert(d <= c);
                    assert(c as int - x as int >= x as int - d as int);
                    assert(!Self::closer(c, d, x));
                }
            }
            res
        }
    }
}

}
