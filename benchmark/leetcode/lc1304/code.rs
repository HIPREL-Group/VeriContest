impl Solution {
    pub fn sum_zero(n: i32) -> Vec<i32> {
        let mut ans: Vec<i32> = Vec::new();
        let half = n / 2;
        let mut i: i32 = 1;
        while i <= half {
            let i0 = i;
            ans.push(i0);
            let neg_i0: i32 = -i0;
            ans.push(neg_i0);
            i = i + 1;
        }
        if n % 2 == 1 {
            ans.push(0);
        }
        ans
    }
}
