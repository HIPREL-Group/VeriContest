use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn daily_temperatures(temperatures: Vec<i32>) -> (res: Vec<i32>)
        requires
            1 <= temperatures.len() <= 100_000,
            forall |i: int| 0 <= i < temperatures.len() ==> 30 <= #[trigger] temperatures[i] <= 100,
        ensures
            res.len() == temperatures.len(),
            forall |i: int| 0 <= i < temperatures.len() ==>
                0 <= #[trigger] res[i] && res[i] as int <= temperatures.len() - 1 - i
                && if res[i] == 0 {
                    forall |j: int| i < j < temperatures.len() ==> temperatures[j] <= temperatures[i]
                } else {
                    let d = res[i] as int;
                    1 <= d && i + d < temperatures.len()
                    && temperatures[i + d] > temperatures[i]
                    && forall |j: int| i < j < i + d ==> temperatures[j] <= temperatures[i]
                },
    {
    }
}

}
