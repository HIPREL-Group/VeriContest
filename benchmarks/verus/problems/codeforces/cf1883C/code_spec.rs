use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn has_even_upto(s: Seq<i32>, i: int) -> bool
    decreases i
{
    if i <= 0 {
        false
    } else {
        (s[i - 1] as int) % 2 == 0 || has_even_upto(s, i - 1)
    }
}

pub open spec fn min_ops_k2(s: Seq<i32>, n: int) -> int {
    if has_even_upto(s, n) {
        0
    } else {
        1
    }
}

pub open spec fn dist_mod3(x: int) -> int {
    let r = x % 3;
    if r == 0 {
        0
    } else {
        3 - r
    }
}

pub open spec fn min_dist_mod3_upto(s: Seq<i32>, i: int) -> int
    decreases i
{
    if i <= 0 {
        3
    } else {
        let prev = min_dist_mod3_upto(s, i - 1);
        let x = s[i - 1] as int;
        let d = dist_mod3(x);
        if d < prev {
            d
        } else {
            prev
        }
    }
}

pub open spec fn dist_mod5(x: int) -> int {
    let r = x % 5;
    if r == 0 {
        0
    } else {
        5 - r
    }
}

pub open spec fn min_dist_mod5_upto(s: Seq<i32>, i: int) -> int
    decreases i
{
    if i <= 0 {
        5
    } else {
        let prev = min_dist_mod5_upto(s, i - 1);
        let x = s[i - 1] as int;
        let d = dist_mod5(x);
        if d < prev {
            d
        } else {
            prev
        }
    }
}

pub open spec fn count_even_upto(s: Seq<i32>, i: int) -> int
    decreases i
{
    if i <= 0 {
        0
    } else {
        let add = if (s[i - 1] as int) % 2 == 0 {
            1int
        } else {
            0int
        };
        count_even_upto(s, i - 1) + add
    }
}

pub open spec fn has_div4_upto(s: Seq<i32>, i: int) -> bool
    decreases i
{
    if i <= 0 {
        false
    } else {
        (s[i - 1] as int) % 4 == 0 || has_div4_upto(s, i - 1)
    }
}

pub open spec fn has_three_mod4_upto(s: Seq<i32>, i: int) -> bool
    decreases i
{
    if i <= 0 {
        false
    } else {
        (s[i - 1] as int) % 4 == 3 || has_three_mod4_upto(s, i - 1)
    }
}

pub open spec fn min_ops_k4(s: Seq<i32>, n: int) -> int {
    if has_div4_upto(s, n) {
        0
    } else if count_even_upto(s, n) >= 2 {
        0
    } else if count_even_upto(s, n) == 1 {
        1
    } else if has_three_mod4_upto(s, n) {
        1
    } else {
        2
    }
}

pub open spec fn expected_min_ops(k: int, s: Seq<i32>, n: int) -> int {
    if k == 2 {
        min_ops_k2(s, n)
    } else if k == 3 {
        min_dist_mod3_upto(s, n)
    } else if k == 4 {
        min_ops_k4(s, n)
    } else if k == 5 {
        min_dist_mod5_upto(s, n)
    } else {
        0
    }
}

pub struct Solution;

impl Solution {
    pub fn min_ops(n: usize, k: i32, a: Vec<i32>) -> (res: i32)
        requires
            2 <= n && n <= 100000,
            2 <= k && k <= 5,
            a.len() == n,
            forall|j: int| 0 <= j && j < n ==> 1 <= a@[j] && a@[j] <= 10,
        ensures
            res == expected_min_ops(k as int, a@, n as int)
    {
        if k == 2 {
            let mut any_even = false;
            let mut i: usize = 0;
            while i < n {
                if a[i] % 2 == 0 {
                    any_even = true;
                }
                i += 1;
            }
            if any_even {
                0
            } else {
                1
            }
        } else if k == 3 {
            let mut best: i32 = 3;
            let mut i: usize = 0;
            while i < n {
                let x = a[i];
                let r = x % 3;
                let cost = if r == 0 { 0 } else { 3 - r };
                if cost < best {
                    best = cost;
                }
                i += 1;
            }
            best
        } else if k == 5 {
            let mut best: i32 = 5;
            let mut i: usize = 0;
            while i < n {
                let x = a[i];
                let r = x % 5;
                let cost = if r == 0 { 0 } else { 5 - r };
                if cost < best {
                    best = cost;
                }
                i += 1;
            }
            best
        } else {
            let mut cnt_even: i32 = 0;
            let mut has4 = false;
            let mut has3mod4 = false;
            let mut i: usize = 0;
            while i < n {
                let old_c = cnt_even;
                let x = a[i];
                if x % 4 == 0 {
                    has4 = true;
                }
                if x % 4 == 3 {
                    has3mod4 = true;
                }
                if x % 2 == 0 {
                    cnt_even = old_c + 1;
                }
                i += 1;
            }
            if has4 {
                0
            } else if cnt_even >= 2 {
                0
            } else if cnt_even == 1 {
                1
            } else if has3mod4 {
                1
            } else {
                2
            }
        }
    }
}

}
