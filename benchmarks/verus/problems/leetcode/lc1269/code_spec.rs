use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn MOD() -> int {
        1_000_000_007
    }

    pub open spec fn max_pos_spec(steps: int, arr_len: int) -> int {
        if steps / 2 < arr_len - 1 {
            steps / 2
        } else {
            arr_len - 1
        }
    }

    pub open spec fn ways(step: int, pos: int, max_pos: int) -> int
        decreases step,
    {
        if step < 0 || pos < 0 || pos > max_pos {
            0
        } else if step == 0 {
            if pos == 0 { 1 } else { 0 }
        } else {
            Self::ways(step - 1, pos - 1, max_pos)
                + Self::ways(step - 1, pos, max_pos)
                + Self::ways(step - 1, pos + 1, max_pos)
        }
    }

    pub fn num_ways(steps: i32, arr_len: i32) -> (result: i32)
        requires
            1 <= steps <= 500,
            1 <= arr_len <= 1_000_000,
        ensures
            result as int == Self::ways(
                steps as int,
                0,
                Self::max_pos_spec(steps as int, arr_len as int),
            ) % Self::MOD(),
    {
        let modulo: i64 = 1_000_000_007;
        let max_p: i32 = if steps / 2 < arr_len - 1 {
            steps / 2
        } else {
            arr_len - 1
        };
        let size: usize = (max_p + 1) as usize;

        let mut cur: Vec<i64> = Vec::new();
        let mut init_i: usize = 0;
        while init_i < size {
            cur.push(0i64);
            init_i += 1;
        }
        cur.set(0, 1i64);

        let mut s: i32 = 0;
        while s < steps {
            let mut nxt: Vec<i64> = Vec::new();
            let mut init_j: usize = 0;
            while init_j < size {
                nxt.push(0i64);
                init_j += 1;
            }
            let mut j: i32 = 0;
            while j <= max_p {
                let left: i64 = if j > 0 {
                    cur[(j - 1) as usize]
                } else {
                    0i64
                };
                let right: i64 = if j < max_p {
                    cur[(j + 1) as usize]
                } else {
                    0i64
                };
                let stay: i64 = cur[j as usize];
                nxt.set(j as usize, (left + right + stay) % modulo);
                j += 1;
            }
            cur = nxt;
            s += 1;
        }
        cur[0] as i32
    }
}

}
