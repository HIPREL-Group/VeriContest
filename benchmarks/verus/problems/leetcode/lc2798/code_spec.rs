use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn number_of_employees_who_met_target(hours: Vec<i32>, target: i32) -> (res: i32) 
        requires 
            1 <= hours.len() <= 50, 
            0 <= target <= 100_000, 
            forall |i: int| 0 <= i < hours.len() ==> 0 <= #[trigger] hours[i] <= 100_000,
        ensures
            res as int == hours@.filter(|h: i32| h >= target).len(),
            0 <= res <= hours.len(), 
    {
        let mut count = 0;
        for i in 0..hours.len() 
        {
            if hours[i] >= target { count += 1; }
        }
        count
    }
}

}