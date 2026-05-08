use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn bounded_temps(temps: Seq<i32>) -> bool {
    forall |i: int| 0 <= i < temps.len() ==> 30 <= #[trigger] temps[i] <= 100
}

pub open spec fn correct_at(temps: Seq<i32>, res: Seq<i32>, k: int) -> bool {
    0 <= k < temps.len()
    && 0 <= res[k]
    && res[k] <= temps.len() - 1 - k
    && if res[k] == 0 {
        forall |m: int| k < m < temps.len() ==> temps[m] <= temps[k]
    } else {
        let d = res[k] as int;
        1 <= d && k + d < temps.len()
        && temps[k + d] > temps[k]
        && forall |m: int| k < m < k + d ==> temps[m] <= temps[k]
    }
}

pub open spec fn next_pos_ok_for(temps: Seq<i32>, start: int, next: Seq<usize>, t: int) -> bool {
    0 <= t < next.len()
    && start <= (next[t] as int)
    && (next[t] as int) <= temps.len()
    && (if (next[t] as int) < temps.len() {
        temps[next[t] as int] == t as i32
        && forall |m: int| start <= m < (next[t] as int) ==> temps[m] != t as i32
    } else {
        forall |m: int| start <= m < temps.len() ==> temps[m] != t as i32
    })
}

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
