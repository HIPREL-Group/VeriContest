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

    proof fn digit_sum_nonneg(x: int)
        ensures Self::digit_sum(x) >= 0
        decreases x
    {
        if x > 0 {
            Self::digit_sum_nonneg(x / 10);
        }
    }

    proof fn digit_sum_le_36(x: int)
        requires 0 <= x <= 10000
        ensures Self::digit_sum(x) <= 36
        decreases x
    {
        if x <= 0 { return; }
        Self::digit_sum_nonneg(x / 10);
        if x <= 9 {
            
        } else if x <= 99 {
            Self::digit_sum_le_9(x / 10);
        } else if x <= 999 {
            Self::digit_sum_le_18(x / 10);
        } else if x <= 9999 {
            Self::digit_sum_le_27(x / 10);
        } else {
            
            Self::digit_sum_le_36(x / 10);
        }
    }

    proof fn digit_sum_le_9(x: int)
        requires 0 <= x <= 9
        ensures Self::digit_sum(x) <= 9
    {
        if x > 0 {
            assert(x / 10 == 0) by(nonlinear_arith) requires 0 < x <= 9;
            assert(x % 10 == x) by(nonlinear_arith) requires 0 <= x <= 9;
            reveal_with_fuel(Solution::digit_sum, 2);
        }
    }

    proof fn digit_sum_le_18(x: int)
        requires 0 <= x <= 99
        ensures Self::digit_sum(x) <= 18
        decreases x
    {
        if x > 0 {
            assert(x / 10 <= 9) by(nonlinear_arith) requires x <= 99, x >= 0;
            Self::digit_sum_le_9(x / 10);
        }
    }

    proof fn digit_sum_le_27(x: int)
        requires 0 <= x <= 999
        ensures Self::digit_sum(x) <= 27
        decreases x
    {
        if x > 0 {
            assert(x / 10 <= 99) by(nonlinear_arith) requires x <= 999, x >= 0;
            Self::digit_sum_le_18(x / 10);
        }
    }

    proof fn digit_sum_pos(x: int)
        requires 1 <= x <= 10000
        ensures Self::digit_sum(x) >= 1
        decreases x
    {
        Self::digit_sum_nonneg(x / 10);
        if x % 10 >= 1 {
        } else {
            assert(x >= 10) by(nonlinear_arith) requires x >= 1, x % 10 == 0;
            assert(x / 10 >= 1) by(nonlinear_arith) requires x >= 10;
            assert(x / 10 <= 10000) by(nonlinear_arith) requires x <= 10000;
            Self::digit_sum_pos(x / 10);
        }
    }

    proof fn group_size_nonneg(n: int, target: int)
        ensures Self::group_size(n, target) >= 0
        decreases n
    {
        if n > 0 { Self::group_size_nonneg(n - 1, target); }
    }

    proof fn group_size_bounded(n: int, target: int)
        requires n >= 0
        ensures Self::group_size(n, target) <= n
        decreases n
    {
        if n > 0 { Self::group_size_bounded(n - 1, target); }
    }

    proof fn count_max_zero_above(n: int, s: int, max_sz: int)
        requires max_sz > Self::max_group_size(n, s)
        ensures Self::count_max_groups(n, s, max_sz) == 0
        decreases s
    {
        if s > 0 {
            Self::group_size_nonneg(n, s);
            Self::count_max_zero_above(n, s - 1, max_sz);
        }
    }

    proof fn count_max_nonneg(n: int, s: int, max_sz: int)
        ensures Self::count_max_groups(n, s, max_sz) >= 0
        decreases s
    {
        if s > 0 { Self::count_max_nonneg(n, s - 1, max_sz); }
    }

    proof fn count_max_bounded(n: int, s: int, max_sz: int)
        requires s >= 0
        ensures Self::count_max_groups(n, s, max_sz) <= s
        decreases s
    {
        if s > 0 { Self::count_max_bounded(n, s - 1, max_sz); }
    }

    proof fn group_size_pos_1(n: int)
        requires n >= 1
        ensures Self::group_size(n, 1) >= 1
        decreases n
    {
        Self::group_size_nonneg(n - 1, 1);
        if n == 1 {
            assert(1int / 10 == 0) by(nonlinear_arith);
            reveal_with_fuel(Solution::digit_sum, 2);
            assert(Self::digit_sum(1) == 1);
        } else if Self::digit_sum(n) == 1 {
        } else {
            Self::group_size_pos_1(n - 1);
        }
    }

    proof fn max_group_ge(n: int, s: int, t: int)
        requires 1 <= t <= s
        ensures Self::max_group_size(n, s) >= Self::group_size(n, t)
        decreases s
    {
        Self::group_size_nonneg(n, s);
        if s > t { Self::max_group_ge(n, s - 1, t); }
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
            invariant
                counts.len() == k, k <= 37,
                forall |idx: int| 0 <= idx < k as int ==> counts[idx] == 0i32,
            decreases 37 - k,
        {
            counts.push(0);
            k = k + 1;
        }

        let mut i: i32 = 1;
        while i <= n
            invariant
                1 <= i <= n + 1, 1 <= n <= 10000,
                counts.len() == 37,
                forall |s: int| 0 <= s < 37
                    ==> #[trigger] counts[s] as int == Self::group_size((i - 1) as int, s),
                forall |s: int| 0 <= s < 37 ==> 0 <= #[trigger] counts[s] <= 10000,
            decreases (n - i + 1),
        {
            let mut ds: i32 = 0;
            let mut x: i32 = i;
            while x > 0
                invariant
                    0 <= ds <= 36,
                    0 <= x <= 10000,
                    1 <= i <= 10000,
                    ds as int + Self::digit_sum(x as int) == Self::digit_sum(i as int),
                decreases x,
            {
                proof {
                    Self::digit_sum_nonneg(x as int / 10);
                    Self::digit_sum_le_36(i as int);
                    assert(ds as int <= Self::digit_sum(i as int));
                }
                ds = ds + (x % 10) as i32;
                x = x / 10;
            }
            proof {
                assert(ds as int == Self::digit_sum(i as int));
                Self::digit_sum_le_36(i as int);
                Self::digit_sum_pos(i as int);
            }
            counts.set(ds as usize, counts[ds as usize] + 1);
            proof {
                assert forall |s: int| 0 <= s < 37
                    implies #[trigger] counts[s] as int == Self::group_size(i as int, s)
                by {
                    Self::group_size_nonneg((i - 1) as int, s);
                };
                assert forall |s: int| 0 <= s < 37
                    implies 0 <= #[trigger] counts[s] <= 10000
                by {
                    Self::group_size_bounded(i as int, s);
                };
            }
            i = i + 1;
        }

        let mut max_size: i32 = 0;
        let mut count: i32 = 0;
        let mut j: usize = 1;
        while j < 37
            invariant
                1 <= j <= 37,
                counts.len() == 37, 1 <= n <= 10000,
                forall |s: int| 0 <= s < 37
                    ==> #[trigger] counts[s] as int == Self::group_size(n as int, s),
                forall |s: int| 0 <= s < 37 ==> 0 <= #[trigger] counts[s] <= 10000,
                max_size as int == Self::max_group_size(n as int, (j - 1) as int),
                0 <= max_size <= 10000,
                max_size > 0 ==> count as int == Self::count_max_groups(
                    n as int, (j - 1) as int, max_size as int,
                ),
                max_size == 0 ==> count == 0,
                0 <= count <= 36,
            decreases 37 - j,
        {
            proof { Self::group_size_nonneg(n as int, j as int); }
            if counts[j] > max_size {
                proof {
                    Self::count_max_zero_above(n as int, (j - 1) as int, counts[j as int] as int);
                }
                max_size = counts[j];
                count = 1;
            } else if counts[j] == max_size && max_size > 0 {
                proof {
                    Self::count_max_nonneg(n as int, (j - 1) as int, max_size as int);
                    Self::count_max_bounded(n as int, (j - 1) as int, max_size as int);
                }
                count = count + 1;
            }
            j = j + 1;
        }
        proof {
            Self::group_size_pos_1(n as int);
            Self::max_group_ge(n as int, 36, 1);
            assert(max_size > 0);
        }
        count
    }
}

}