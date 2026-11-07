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
    }
}

}
