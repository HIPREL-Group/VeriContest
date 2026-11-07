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
    }

    pub fn length(&self) -> (result: i32)
        requires
            self.data@.len() <= 10_000,
        ensures
            result as int == self.data@.len(),
    {
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
    }
}

}
