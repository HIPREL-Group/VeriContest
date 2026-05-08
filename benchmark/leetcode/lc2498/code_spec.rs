use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn max_jump_spec(stones: Seq<i32>, odd: int, even: int, current_max: int) -> int
        decreases stones.len() + 1 - odd
    {
        if odd >= stones.len() {
            current_max
        } else {
            let odd_target = if odd + 2 < stones.len() - 1 { odd + 2 } else { (stones.len() - 1) as int };
            let odd_jump = stones[odd_target] - stones[odd];
            let new_max1 = if current_max > odd_jump { current_max } else { odd_jump };
            
            let even_target = if even + 2 < stones.len() - 1 { even + 2 } else { (stones.len() - 1) as int };
            let even_jump = stones[even_target] - stones[even];
            let new_max2 = if new_max1 > even_jump { new_max1 } else { even_jump };
            
            Self::max_jump_spec(stones, odd + 2, even + 2, new_max2)
        }
    }

    pub fn max_jump(stones: Vec<i32>) -> (res: i32) 
        requires 
            2 <= stones.len() <= 100_000, 
            forall |i: int| 0 <= i < stones.len() ==> 0 <= #[trigger] stones[i] <= 1_000_000_000,
            stones[0] == 0, 
            forall |i: int, j: int| 0 <= i < j < stones.len() ==> stones[i] < stones[j],
        ensures 
            res == Self::max_jump_spec(stones@, 1, 0, 0),
    {
        let mut ans = 0;
        let len = stones.len();
        let mut odd = 1;
        let mut even = 0;
        while odd < len 
        {
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

}