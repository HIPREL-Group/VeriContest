impl Solution {
    fn add_mod(x: i32, y: i32) -> i32 {
        let sum = x + y;
        if sum >= 1_000_000_007i32 {
            sum - 1_000_000_007i32
        } else {
            sum
        }
    }

    fn sub_mod(x: i32, y: i32) -> i32 {
        if x >= y {
            x - y
        } else {
            x + 1_000_000_007i32 - y
        }
    }

    pub fn solve_queries(k: i32, lefts: Vec<i32>, rights: Vec<i32>) -> Vec<i32> {
        let max_n = 100_000usize;
        let mut ways = Vec::new();
        ways.push(1);
        let mut prefix = Vec::new();
        prefix.push(0);
        let mut len = 1usize;
        while len <= max_n {
            let prev = ways[len - 1];
            let next = if len < k as usize {
                prev
            } else {
                Self::add_mod(prev, ways[len - k as usize])
            };
            let next_prefix = Self::add_mod(prefix[len - 1], next);
            ways.push(next);
            prefix.push(next_prefix);
            len += 1;
        }
        let mut answers = Vec::new();
        let mut idx = 0usize;
        while idx < lefts.len() {
            let left = lefts[idx];
            let right = rights[idx];
            let answer = if left == 1 {
                prefix[right as usize]
            } else {
                Self::sub_mod(prefix[right as usize], prefix[left as usize - 1])
            };
            answers.push(answer);
            idx += 1;
        }
        answers
    }
}
