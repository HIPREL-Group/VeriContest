use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    
    
    
    
    
    
    
    pub open spec fn dp_val(i: int, j: int, rm: Seq<i32>) -> int
        recommends 0 <= j < 6, rm.len() == 6,
        decreases i, 17int,
    {
        if i <= 0 { 0 }
        else if i == 1 { 1 }
        else {
            Self::dp_acc(i, j, 1, rm)
        }
    }

    
    
    pub open spec fn dp_acc(i: int, j: int, k: int, rm: Seq<i32>) -> int
        recommends 0 <= j < 6, rm.len() == 6,
        decreases i, 16int - k,
    {
        if k < 1 || k > rm[j] as int || k > i || k > 15 { 0 }
        else {
            let p = i - k;
            (
                (if p <= 0 { 1int } else { 0 })
                + Self::dp_val(p, 0, rm) + Self::dp_val(p, 1, rm)
                + Self::dp_val(p, 2, rm) + Self::dp_val(p, 3, rm)
                + Self::dp_val(p, 4, rm) + Self::dp_val(p, 5, rm)
                - Self::dp_val(p, j, rm)
            ) + Self::dp_acc(i, j, k + 1, rm)
        }
    }

    
    pub open spec fn total_val(i: int, rm: Seq<i32>) -> int
        recommends rm.len() == 6,
    {
        if i <= 0 { 1 }
        else {
            Self::dp_val(i, 0, rm) + Self::dp_val(i, 1, rm) + Self::dp_val(i, 2, rm)
                + Self::dp_val(i, 3, rm) + Self::dp_val(i, 4, rm) + Self::dp_val(i, 5, rm)
        }
    }

    pub fn die_simulator(n: i32, roll_max: Vec<i32>) -> (result: i32)
        requires
            1 <= n <= 5000,
            roll_max.len() == 6,
            forall |j: int| 0 <= j < 6 ==> 1 <= #[trigger] roll_max[j] <= 15,
        ensures
            0 <= result < 1_000_000_007,
            result as int == Solution::total_val(n as int, roll_max@) % 1_000_000_007,
    {
    }
}

}
