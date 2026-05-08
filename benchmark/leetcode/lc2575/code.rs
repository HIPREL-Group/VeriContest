impl Solution {
    pub fn divisibility_array(word: String, m: i32) -> Vec<i32> {
        let n = word.as_str().unicode_len();
        let mm: i64 = m as i64;
        let mut rem: i64 = 0;
        let mut i: usize = 0;
        let mut res: Vec<i32> = Vec::new();

        while i < n {
            let d = (word.as_str().get_char(i) as i64) - ('0' as i64);
            rem = (rem * 10 + d) % mm;
            if rem == 0 {
                res.push(1);
            } else {
                res.push(0);
            }
            i = i + 1;
        }

        res
    }
}
