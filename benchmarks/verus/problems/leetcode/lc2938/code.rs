impl Solution {
    pub fn minimum_steps(s: String) -> i64 {
        let len = s.as_str().unicode_len();
        let mut i: usize = 0;
        let mut ones: i64 = 0;
        let mut steps: i64 = 0;

        while i < len {
            let c = s.as_str().get_char(i);
            if c == '1' {
                ones = ones + 1;
            } else {
                steps = steps + ones;
            }
            i = i + 1;
        }

        steps
    }
}
