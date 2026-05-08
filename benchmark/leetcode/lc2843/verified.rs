use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_symmetric_num(x: int) -> bool {
        if 10 <= x <= 99 {
            x / 10 == x % 10
        } else if 1000 <= x <= 9999 {
            x / 1000 + (x / 100) % 10 == (x / 10) % 10 + x % 10
        } else {
            false
        }
    }

    pub open spec fn contrib(x: int) -> int {
        if Self::is_symmetric_num(x) { 1 } else { 0 }
    }

    pub open spec fn count_symmetric_range(low: int, high: int) -> int
        decreases if high < low { 0int } else { high - low + 1 }
    {
        if high < low {
            0
        } else {
            Self::count_symmetric_range(low, high - 1) + Self::contrib(high)
        }
    }

    fn is_symmetric(x: i32) -> (res: bool)
        requires
            1 <= x <= 10_000,
        ensures
            res == Self::is_symmetric_num(x as int),
    {
        if x >= 10 && x <= 99 {
            x / 10 == x % 10
        } else if x >= 1000 && x <= 9999 {
            let left = x / 1000 + (x / 100) % 10;
            let right = (x / 10) % 10 + x % 10;
            left == right
        } else {
            false
        }
    }

    pub fn count_symmetric_integers(low: i32, high: i32) -> (result: i32)
        requires
            1 <= low <= high <= 10_000,
        ensures
            result as int == Self::count_symmetric_range(low as int, high as int),
    {
        let mut i = low;
        let mut count = 0i32;
        while i <= high
            invariant
                1 <= low <= high <= 10_000,
                low <= i <= high + 1,
                0 <= count <= i - low,
                count as int == Self::count_symmetric_range(low as int, i as int - 1),
            decreases high - i + 1,
        {
            let old_i = i;
            let is_sym = Self::is_symmetric(i);
            if is_sym {
                count = count + 1;
            }
            i = i + 1;
            proof {
                assert(Self::count_symmetric_range(low as int, old_i as int)
                    == Self::count_symmetric_range(low as int, old_i as int - 1)
                        + Self::contrib(old_i as int));
                assert(is_sym == Self::is_symmetric_num(old_i as int));
                if is_sym {
                    assert(Self::contrib(old_i as int) == 1);
                } else {
                    assert(Self::contrib(old_i as int) == 0);
                }
            }
        }
        count
    }
}

}
