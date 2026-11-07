impl Solution {
    pub fn num_equiv_domino_pairs(dominoes: Vec<Vec<i32>>) -> i32 {
        let n = dominoes.len();
        let mut counts: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        while idx < 100 {
            counts.push(0);
            idx = idx + 1;
        }
        let mut result: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            let a = dominoes[i][0];
            let b = dominoes[i][1];
            let lo = if a <= b { a } else { b };
            let hi = if a <= b { b } else { a };
            let key = (lo * 10 + hi) as usize;
            result = result + counts[key];
            counts[key] = counts[key] + 1;
            i = i + 1;
        }
        result
    }
}
