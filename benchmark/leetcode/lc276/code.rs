impl Solution {
    pub fn num_ways(n: i32, k: i32) -> i32 {
        if n == 0 {
            return 0;
        }
        if n == 1 {
            return k;
        }

        let mut prev2: i32 = k;
        let mut prev1: i32 = k * k;
        let mut i: i32 = 3;
        while i <= n {
            let sum = prev1 + prev2;
            let next = (k - 1) * sum;
            prev2 = prev1;
            prev1 = next;
            i = i + 1;
        }
        prev1
    }
}
