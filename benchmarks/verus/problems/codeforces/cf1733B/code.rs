impl Solution {
    pub fn rule_of_league(n: i64, x: i64, y: i64) -> Option<Vec<i64>> {
        let lo = if x < y { x } else { y };
        let hi = if x > y { x } else { y };
        if lo != 0 {
            return None;
        }
        if hi == 0 {
            return None;
        }
        if (n - 1) % hi != 0 {
            return None;
        }
        let m = (n - 1) as usize;
        let mut w: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < m {
            let ii = i as i64;
            let block = ii / hi;
            let win = 2 + block * hi;
            w.push(win);
            i = i + 1;
        }
        let out = Some(w);
        out
    }
}
