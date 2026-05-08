impl Solution {
    pub fn max_beauty_and_pair_count(flowers: Vec<i64>) -> (i64, i64) {
        let mut min_val = flowers[0];
        let mut max_val = flowers[0];
        let mut min_count = 1i64;
        let mut max_count = 1i64;
        let mut i = 1usize;
        while i < flowers.len() {
            let x = flowers[i];
            if x < min_val {
                min_val = x;
                min_count = 1;
            } else if x == min_val {
                min_count += 1;
            }
            if x > max_val {
                max_val = x;
                max_count = 1;
            } else if x == max_val {
                max_count += 1;
            }
            i += 1;
        }
        let diff = max_val - min_val;
        let n = flowers.len() as i64;
        let pair_count = if min_val == max_val {
            n * (n - 1) / 2
        } else {
            min_count * max_count
        };
        (diff, pair_count)
    }
}
