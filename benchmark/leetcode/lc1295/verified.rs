use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn has_even_digits(x: int) -> bool {
    (10 <= x && x <= 99) || (1000 <= x && x <= 9999) || x == 100000
}

pub open spec fn count_even(s: Seq<i32>, end: int) -> int
    decreases end,
{
    if end <= 0 {
        0
    } else {
        count_even(s, end - 1) + if has_even_digits(s[end - 1] as int) { 1int } else { 0int }
    }
}

proof fn count_even_bounds(s: Seq<i32>, end: int)
    requires
        0 <= end <= s.len(),
    ensures
        0 <= count_even(s, end) <= end,
    decreases end,
{
    if end > 0 {
        count_even_bounds(s, end - 1);
    }
}

impl Solution {
    pub fn find_numbers(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 500,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100000,
        ensures
            result as int == count_even(nums@, nums.len() as int),
    {
        let n = nums.len();
        let mut count: i32 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                n == nums.len(),
                0 <= i <= n,
                1 <= nums.len() <= 500,
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100000,
                count as int == count_even(nums@, i as int),
                0 <= count_even(nums@, i as int) <= i as int,
            decreases n - i,
        {
            proof {
                count_even_bounds(nums@, i as int);
                assert(count_even(nums@, (i + 1) as int) == count_even(nums@, i as int) + if has_even_digits(nums@[i as int] as int) { 1int } else { 0int });
            }
            let x = nums[i];
            if (x >= 10 && x <= 99) || (x >= 1000 && x <= 9999) || x == 100000 {
                count = count + 1;
            }
            i = i + 1;
        }
        proof {
            count_even_bounds(nums@, n as int);
        }
        count
    }
}

}
