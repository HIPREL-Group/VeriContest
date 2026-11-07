use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn digit_sum(x: int) -> int
        decreases x,
    {
        if x <= 0 { 0 }
        else { x % 10 + Self::digit_sum(x / 10) }
    }

    pub open spec fn group_size(n: int, target: int) -> int
        decreases n,
    {
        if n <= 0 { 0 }
        else {
            (if Self::digit_sum(n) == target { 1int } else { 0int })
                + Self::group_size(n - 1, target)
        }
    }

    pub open spec fn max_group_size(n: int, s: int) -> int
        decreases s,
    {
        if s <= 0 { 0 }
        else {
            let prev = Self::max_group_size(n, s - 1);
            let cur = Self::group_size(n, s);
            if cur > prev { cur } else { prev }
        }
    }

    pub open spec fn count_max_groups(n: int, s: int, max_sz: int) -> int
        decreases s,
    {
        if s <= 0 { 0 }
        else {
            (if Self::group_size(n, s) == max_sz { 1int } else { 0int })
                + Self::count_max_groups(n, s - 1, max_sz)
        }
    }

    pub fn count_largest_group(n: i32) -> (result: i32)
        requires 1 <= n <= 10000
        ensures
            result as int == Self::count_max_groups(
                n as int, 36, Self::max_group_size(n as int, 36),
            ),
    {
        let mut counts: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < 37
        {
            counts.push(0);
            k = k + 1;
        }
        let mut i: i32 = 1;
        while i <= n
        {
            let mut ds: i32 = 0;
            let mut x: i32 = i;
            while x > 0
            {
                ds = ds + (x % 10) as i32;
                x = x / 10;
            }
            counts.set(ds as usize, counts[ds as usize] + 1);
            i = i + 1;
        }
        let mut max_size: i32 = 0;
        let mut count: i32 = 0;
        let mut j: usize = 1;
        while j < 37
        {
            if counts[j] > max_size {
                max_size = counts[j];
                count = 1;
            } else if counts[j] == max_size && max_size > 0 {
                count = count + 1;
            }
            j = j + 1;
        }
        count
    }
}

}