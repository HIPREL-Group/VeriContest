use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_occurrences(arr: Seq<i32>, left: int, right: int, val: i32) -> int
        decreases right - left + 1
    {
        if left > right {
            0
        } else if arr[left] == val {
            1 + Self::count_occurrences(arr, left + 1, right, val)
        } else {
            Self::count_occurrences(arr, left + 1, right, val)
        }
    }
}

pub struct MajorityChecker {
    pub arr: Vec<i32>,
}

impl MajorityChecker {
    pub fn new(arr: Vec<i32>) -> (result: Self)
        requires
            1 <= arr.len() <= 20_000,
            forall |i: int| 0 <= i < arr@.len() ==> 1 <= #[trigger] arr@[i] <= 20_000,
        ensures
            result.arr@ == arr@,
    {
        MajorityChecker { arr }
    }

    pub fn query(&self, left: i32, right: i32, threshold: i32) -> (result: i32)
        requires
            1 <= self.arr.len() <= 20_000,
            forall |i: int| 0 <= i < self.arr@.len() ==> 1 <= #[trigger] self.arr@[i] <= 20_000,
            0 <= left <= right,
            right < self.arr.len() as i32,
            threshold >= 1,
            threshold <= right - left + 1,
            2 * threshold > right - left + 1,
        ensures
            result == -1 || (
                1 <= result <= 20_000
                && Solution::count_occurrences(self.arr@, left as int, right as int, result) >= threshold as int
            ),
            result == -1 ==> forall |v: i32| 1 <= v <= 20_000 ==>
                Solution::count_occurrences(self.arr@, left as int, right as int, v) < threshold as int,
    {
        let l = left as usize;
        let r = right as usize;
        let mut candidate: i32 = self.arr[l];
        let mut cnt: i32 = 0;
        let mut i: usize = l;
        while i <= r {
            if cnt == 0 {
                candidate = self.arr[i];
                cnt = 1;
            } else if self.arr[i] == candidate {
                cnt = cnt + 1;
            } else {
                cnt = cnt - 1;
            }
            i = i + 1;
        }
        let mut actual_count: i32 = 0;
        let mut j: usize = l;
        while j <= r {
            if self.arr[j] == candidate {
                actual_count = actual_count + 1;
            }
            j = j + 1;
        }
        if actual_count >= threshold {
            candidate
        } else {
            -1
        }
    }
}

}
