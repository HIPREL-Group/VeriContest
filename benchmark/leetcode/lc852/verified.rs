use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_mountain(s: Seq<i32>, peak: int) -> bool {
        s.len() >= 3
        && 0 < peak < s.len() - 1
        && (forall |a: int, b: int| 0 <= a < b <= peak ==> s[a] < s[b])
        && (forall |a: int, b: int| peak <= a < b < s.len() ==> s[a] > s[b])
    }

    pub fn peak_index_in_mountain_array(arr: Vec<i32>) -> (result: i32)
        requires
            3 <= arr.len() <= 100_000,
            forall |i: int| 0 <= i < arr.len() ==> 0 <= #[trigger] arr[i] <= 1_000_000,
            exists |peak: int| Self::is_mountain(arr@, peak),
        ensures
            0 < result < arr.len() - 1,
            Self::is_mountain(arr@, result as int),
    {
        let n = arr.len();
        let ghost peak_idx: int = choose |p: int| Self::is_mountain(arr@, p);
        let mut left: usize = 0;
        let mut right: usize = n - 1;

        while left < right
            invariant
                0 <= left <= right < n,
                n == arr.len(),
                3 <= n,
                forall |i: int| 0 <= i < n as int ==> 0 <= #[trigger] arr[i] <= 1_000_000,
                Self::is_mountain(arr@, peak_idx),
                left as int <= peak_idx,
                peak_idx <= right as int,
                left == 0 || arr[left as int - 1] < arr[left as int],
                right == n - 1 || arr[right as int] > arr[right as int + 1],
            decreases right - left,
        {
            let mid = left + (right - left) / 2;

            if arr[mid] < arr[mid + 1] {
                proof {
                    
                    
                    if peak_idx <= mid as int {
                        assert(arr@[mid as int] > arr@[mid as int + 1]);
                        assert(false);
                    }
                    assert(peak_idx >= mid as int + 1);
                }
                left = mid + 1;
            } else {
                proof {
                    
                    
                    if peak_idx > mid as int {
                        assert(arr@[mid as int] < arr@[mid as int + 1]);
                        assert(false);
                    }
                    assert(peak_idx <= mid as int);
                    
                    assert(arr@[mid as int] > arr@[mid as int + 1]);
                }
                right = mid;
            }
        }

        proof {
            assert(left as int == peak_idx);
            assert(Self::is_mountain(arr@, left as int));
        }

        left as i32
    }
}

}
