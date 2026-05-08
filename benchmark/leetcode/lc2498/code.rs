impl Solution {
    pub fn max_jump(stones: Vec<i32>) -> i32
    {
        let mut ans = 0;
        let len = stones.len();
        let mut odd = 1;
        let mut even = 0;
        while odd < len {
            let odd_target = if odd + 2 < len - 1 { odd + 2 } else { len - 1 };
            let odd_jump = stones[odd_target] - stones[odd];
            ans = if ans > odd_jump { ans } else { odd_jump };

            let even_target = if even + 2 < len - 1 { even + 2 } else { len - 1 };
            let even_jump = stones[even_target] - stones[even];
            ans = if ans > even_jump { ans } else { even_jump };
            
            odd += 2;
            even += 2;
        }
        ans
    }
}