use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_occurrences(s: Seq<i32>, value: i32) -> nat
        decreases s.len()
    {
        if s.len() == 0 {
            0
        } else {
            Self::count_occurrences(s.drop_last(), value)
                + if s.last() == value { 1 as nat } else { 0 as nat }
        }
    }

    pub fn single_number(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            2 <= nums.len() <= 30_000,
            forall |i: int| 0 <= i < nums.len() ==> -2_147_483_648 <= #[trigger] nums[i] <= 2_147_483_647,
            exists |a: i32, b: i32| {
                a != b
                && Self::count_occurrences(nums@, a) == 1
                && Self::count_occurrences(nums@, b) == 1
                && forall |x: i32| x != a && x != b ==> Self::count_occurrences(nums@, x) == 0 || Self::count_occurrences(nums@, x) == 2
            },
        ensures
            result.len() == 2,
            Self::count_occurrences(nums@, result[0]) == 1,
            Self::count_occurrences(nums@, result[1]) == 1,
    {
        let mut xor_all: i32 = 0;
        let mut i: usize = 0;
        while i < nums.len() {
            xor_all = xor_all ^ nums[i];
            i = i + 1;
        }

        let mut mask: i32 = 1;
        let mut shift: u32 = 0;
        while shift < 31 && (xor_all & mask) == 0 {
            mask = mask << 1;
            shift = shift + 1;
        }

        let mut a: i32 = 0;
        let mut b: i32 = 0;
        let mut j: usize = 0;
        while j < nums.len() {
            if (nums[j] & mask) == 0 {
                a = a ^ nums[j];
            } else {
                b = b ^ nums[j];
            }
            j = j + 1;
        }

        let mut result: Vec<i32> = Vec::new();
        result.push(a);
        result.push(b);
        result
    }
}

}
