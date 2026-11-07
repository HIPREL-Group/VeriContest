use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    

    
    
    pub open spec fn optimal_diff(values: Seq<i32>, i: int) -> int
        decreases values.len() - i
    {
        if i >= values.len() {
            0
        } else {
            let n = values.len() as int;
            let t1 = values[i] as int - Self::optimal_diff(values, i + 1);
            if i + 1 >= n {
                t1
            } else {
                let t2 = values[i] as int + values[i + 1] as int - Self::optimal_diff(values, i + 2);
                if i + 2 >= n {
                    if t1 >= t2 { t1 } else { t2 }
                } else {
                    let t3 = values[i] as int + values[i + 1] as int + values[i + 2] as int - Self::optimal_diff(values, i + 3);
                    if t1 >= t2 && t1 >= t3 { t1 }
                    else if t2 >= t3 { t2 }
                    else { t3 }
                }
            }
        }
    }

    pub fn stone_game_iii(stone_value: Vec<i32>) -> (result: String)
        requires
            1 <= stone_value.len() <= 50_000,
            forall |i: int| 0 <= i < stone_value.len() ==>
                -1000 <= #[trigger] stone_value[i] <= 1000,
        ensures
            Self::optimal_diff(stone_value@, 0) > 0 ==> result@ == "Alice"@,
            Self::optimal_diff(stone_value@, 0) < 0 ==> result@ == "Bob"@,
            Self::optimal_diff(stone_value@, 0) == 0 ==> result@ == "Tie"@,
    {
        let n = stone_value.len();
        let mut dp: Vec<i64> = Vec::new();
        let mut k: usize = 0;
        while k <= n {
            dp.push(0i64);
            k = k + 1;
        }
        let mut i: usize = n;
        while i > 0 {
            i = i - 1;
            let mut best: i64 = stone_value[i] as i64 - dp[i + 1];
            if i + 1 < n {
                let t2: i64 = stone_value[i] as i64 + stone_value[i + 1] as i64 - dp[i + 2];
                if t2 > best {
                    best = t2;
                }
            }
            if i + 2 < n {
                let t3: i64 = stone_value[i] as i64 + stone_value[i + 1] as i64 + stone_value[i + 2] as i64 - dp[i + 3];
                if t3 > best {
                    best = t3;
                }
            }
            dp.set(i, best);
        }
        if dp[0] > 0 {
            "Alice".to_string()
        } else if dp[0] < 0 {
            "Bob".to_string()
        } else {
            "Tie".to_string()
        }
    }
}

}
