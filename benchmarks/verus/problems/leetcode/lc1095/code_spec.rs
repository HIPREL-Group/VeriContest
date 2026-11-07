use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub struct MountainArray {
    pub data: Vec<i32>,
}

impl MountainArray {
    pub fn get(&self, index: i32) -> (result: i32)
        requires
            0 <= index < self.data.len(),
        ensures
            result == self.data@[index as int],
    {
        self.data[index as usize]
    }

    pub fn length(&self) -> (result: i32)
        requires
            self.data@.len() <= 10_000,
        ensures
            result as int == self.data@.len(),
    {
        self.data.len() as i32
    }
}

impl Solution {
    pub open spec fn is_mountain(s: Seq<i32>, peak: int) -> bool {
        s.len() >= 3
        && 0 < peak < s.len() - 1
        && (forall |a: int, b: int| 0 <= a < b <= peak ==> s[a] < s[b])
        && (forall |a: int, b: int| peak <= a < b < s.len() ==> s[a] > s[b])
    }

    pub fn find_in_mountain_array(target: i32, mountain_arr: &MountainArray) -> (result: i32)
        requires
            3 <= mountain_arr.data.len() <= 10_000,
            forall |i: int| 0 <= i < mountain_arr.data.len() ==> 0 <= #[trigger] mountain_arr.data@[i] <= 1_000_000_000,
            0 <= target <= 1_000_000_000,
            exists |peak: int| Self::is_mountain(mountain_arr.data@, peak),
        ensures
            -1 <= result < mountain_arr.data.len(),
            result == -1 ==> forall |j: int| 0 <= j < mountain_arr.data.len() ==> mountain_arr.data@[j] != target,
            result >= 0 ==> (
                mountain_arr.data@[result as int] == target
                && forall |j: int| 0 <= j < result as int ==> mountain_arr.data@[j] != target
            ),
    {
        let n = mountain_arr.length();
        let mut left: i32 = 0;
        let mut right: i32 = n - 1;
        while left < right {
            let mid = left + (right - left) / 2;
            if mountain_arr.get(mid) < mountain_arr.get(mid + 1) {
                left = mid + 1;
            } else {
                right = mid;
            }
        }
        let peak = left;
        let mut lo: i32 = 0;
        let mut hi: i32 = peak + 1;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if mountain_arr.get(mid) < target {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        if lo <= peak && mountain_arr.get(lo) == target {
            return lo;
        }
        lo = peak + 1;
        hi = n;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if mountain_arr.get(mid) > target {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        if lo < n && mountain_arr.get(lo) == target {
            return lo;
        }
        -1
    }
}

}
