impl Solution {
    pub fn daily_temperatures(temperatures: Vec<i32>) -> Vec<i32>
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
