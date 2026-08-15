use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn daily_temperatures(temperatures: Vec<i32>) -> (res: Vec<i32>)
        requires
            1 <= temperatures.len() <= 100_000,
            forall |i: int| 0 <= i < temperatures.len() ==> 30 <= #[trigger] temperatures[i] <= 100,
        ensures
            res.len() == temperatures.len(),
            forall |i: int| 0 <= i < temperatures.len() ==>
                0 <= #[trigger] res[i] && res[i] as int <= temperatures.len() - 1 - i
                && if res[i] == 0 {
                    forall |j: int| i < j < temperatures.len() ==> temperatures[j] <= temperatures[i]
                } else {
                    let d = res[i] as int;
                    1 <= d && i + d < temperatures.len()
                    && temperatures[i + d] > temperatures[i]
                    && forall |j: int| i < j < i + d ==> temperatures[j] <= temperatures[i]
                },
    {
        let n = temperatures.len();

        let mut res: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        while idx < n
        {
            res.push(0);
            idx = idx + 1;
        }

        let mut next_pos: Vec<usize> = Vec::new();
        let mut t0: usize = 0;
        while t0 <= 100
        {
            next_pos.push(n);
            t0 = t0 + 1;
        }

        let mut i: usize = n;
        while i > 0
        {
            let idx = i - 1;
            let cur = temperatures[idx] as usize;
            let mut best: usize = n;
            let mut t: usize = cur + 1;
            while t <= 100
            {
                let candidate = next_pos[t];
                if candidate < best {
                    best = candidate;
                }
                t = t + 1;
            }

            if best < n {
                let d: i32 = (best - idx) as i32;
                res[idx] = d;
            } else {
                res[idx] = 0;
            }

            next_pos[cur] = idx;
            i = idx;
        }

        res
    }
}

}
