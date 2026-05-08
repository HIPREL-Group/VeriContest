use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn pow3(k: int) -> int
    decreases k
{
    if k <= 0 { 1 } else { 3 * pow3(k - 1) }
}

pub open spec fn interaction(me: int, neighbor: int) -> int {
    if neighbor == 0 || me == 0 { 0 }
    else if me == 1 && neighbor == 1 { -60 }
    else if me == 1 && neighbor == 2 { -10 }
    else if me == 2 && neighbor == 1 { -10 }
    else { 40 }
}

pub open spec fn delta_spec(t: int, pos: int, profile: int, m: int, n: int) -> int {
    let row = pos / n;
    let col = pos % n;
    let up_type = profile % 3;
    let left_type = (profile / pow3(n - 1)) % 3;
    let base: int = if t == 1 { 120 } else if t == 2 { 40 } else { 0 };
    base
    + (if row > 0 { interaction(t, up_type) } else { 0 })
    + (if col > 0 { interaction(t, left_type) } else { 0 })
}

pub open spec fn shift_spec(profile: int, new_val: int, n: int) -> int {
    profile / 3 + new_val * pow3(n - 1)
}

pub open spec fn max3(a: int, b: int, c: int) -> int {
    if a >= b && a >= c { a }
    else if b >= c { b }
    else { c }
}

pub open spec fn max_happiness(pos: int, ic: int, ec: int, profile: int, m: int, n: int) -> int
    decreases m * n - pos
{
    if pos >= m * n {
        0
    } else {
        let v_empty = max_happiness(pos + 1, ic, ec, shift_spec(profile, 0, n), m, n);
        let v_intro = if ic > 0 {
            delta_spec(1, pos, profile, m, n)
            + max_happiness(pos + 1, ic - 1, ec, shift_spec(profile, 1, n), m, n)
        } else {
            v_empty
        };
        let v_extro = if ec > 0 {
            delta_spec(2, pos, profile, m, n)
            + max_happiness(pos + 1, ic, ec - 1, shift_spec(profile, 2, n), m, n)
        } else {
            v_empty
        };
        max3(v_empty, v_intro, v_extro)
    }
}

impl Solution {
    pub fn get_max_grid_happiness(m: i32, n: i32, introverts_count: i32, extroverts_count: i32) -> (result: i32)
        requires
            1 <= m <= 5,
            1 <= n <= 5,
            0 <= introverts_count <= 6,
            0 <= extroverts_count <= 6,
            introverts_count <= m * n,
            extroverts_count <= m * n,
        ensures
            result as int == max_happiness(0, introverts_count as int, extroverts_count as int, 0, m as int, n as int),
    {
        let mut pow3nm1: i32 = 1;
        let mut k: i32 = 1;
        while k < n {
            pow3nm1 = pow3nm1 * 3;
            k = k + 1;
        }
        Solution::solve(m, n, 0, introverts_count, extroverts_count, 0, pow3nm1)
    }

    fn solve(m: i32, n: i32, pos: i32, ic: i32, ec: i32, profile: i32, pow3nm1: i32) -> (result: i32)
        requires
            1 <= m <= 5,
            1 <= n <= 5,
            0 <= pos <= m * n,
            0 <= ic <= 6,
            0 <= ec <= 6,
            0 <= profile < pow3(n as int),
            pow3nm1 as int == pow3((n - 1) as int),
            1 <= pow3nm1 <= 81,
        ensures
            result as int == max_happiness(pos as int, ic as int, ec as int, profile as int, m as int, n as int),
        decreases m * n - pos
    {
        if pos >= m * n {
            return 0;
        }
        let row = pos / n;
        let col = pos % n;
        let up_type = profile % 3;
        let left_type = (profile / pow3nm1) % 3;
        let shifted = profile / 3;
        let val_empty = Solution::solve(m, n, pos + 1, ic, ec, shifted, pow3nm1);
        let mut best = val_empty;
        if ic > 0 {
            let base: i32 = 120;
            let adj_up: i32 = if row > 0 {
                if up_type == 0 { 0 } else if up_type == 1 { -60 } else { -10 }
            } else { 0 };
            let adj_left: i32 = if col > 0 {
                if left_type == 0 { 0 } else if left_type == 1 { -60 } else { -10 }
            } else { 0 };
            let d = base + adj_up + adj_left;
            let next_pr = shifted + pow3nm1;
            let val_intro = d + Solution::solve(m, n, pos + 1, ic - 1, ec, next_pr, pow3nm1);
            if val_intro > best {
                best = val_intro;
            }
        }
        if ec > 0 {
            let base: i32 = 40;
            let adj_up: i32 = if row > 0 {
                if up_type == 0 { 0 } else if up_type == 1 { -10 } else { 40 }
            } else { 0 };
            let adj_left: i32 = if col > 0 {
                if left_type == 0 { 0 } else if left_type == 1 { -10 } else { 40 }
            } else { 0 };
            let d = base + adj_up + adj_left;
            let next_pr = shifted + 2 * pow3nm1;
            let val_extro = d + Solution::solve(m, n, pos + 1, ic, ec - 1, next_pr, pow3nm1);
            if val_extro > best {
                best = val_extro;
            }
        }
        best
    }
}

} 
