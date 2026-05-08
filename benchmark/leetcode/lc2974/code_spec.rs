use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_value(nums: Seq<i32>, value: int, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::count_value(nums, value, end - 1)
                + if nums[end - 1] as int == value { 1int } else { 0int }
        }
    }

    pub open spec fn repeat_value(value: int, times: int) -> Seq<i32>
        decreases times,
    {
        if times <= 0 {
            seq![]
        } else {
            Self::repeat_value(value, times - 1).push(value as i32)
        }
    }

    pub open spec fn sorted_values(nums: Seq<i32>, upto: int) -> Seq<i32>
        decreases upto,
    {
        if upto <= 0 {
            seq![]
        } else {
            Self::sorted_values(nums, upto - 1)
                + Self::repeat_value(upto, Self::count_value(nums, upto, nums.len() as int))
        }
    }

    pub open spec fn swapped_pairs(sorted: Seq<i32>, pairs: int) -> Seq<i32>
        decreases pairs,
    {
        if pairs <= 0 {
            seq![]
        } else {
            let prev = Self::swapped_pairs(sorted, pairs - 1);
            let i = 2 * (pairs - 1);
            prev + seq![sorted[i + 1], sorted[i]]
        }
    }

    fn count_value_exec(nums: &Vec<i32>, value: i32) -> (c: i32)
        ensures
            c as int == Self::count_value(nums@, value as int, nums.len() as int),
    {
        let n = nums.len();
        let mut i: usize = 0;
        let mut c: i32 = 0;
        while i < n {
            if nums[i] == value {
                c = c + 1;
            }
            i = i + 1;
        }
        c
    }

    pub fn number_game(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            2 <= nums.len() <= 100,
            nums.len() % 2 == 0,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        ensures
            result@ == Self::swapped_pairs(Self::sorted_values(nums@, 100), (Self::sorted_values(nums@, 100).len() / 2) as int),
    {
        let mut result: Vec<i32> = Vec::new();
        let mut has_pending = false;
        let mut pending: i32 = 0;
        let mut value: i32 = 1;
        while value <= 100 {
            let cnt = Self::count_value_exec(&nums, value);
            let mut t: i32 = 0;
            while t < cnt {
                if has_pending {
                    result.push(value);
                    result.push(pending);
                    has_pending = false;
                } else {
                    pending = value;
                    has_pending = true;
                }
                t = t + 1;
            }
            value = value + 1;
        }
        result
    }
}

}
