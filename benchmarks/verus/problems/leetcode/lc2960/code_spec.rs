use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_count_tested(bp: Seq<i32>, k: int, tested: int) -> int
    decreases bp.len() - k,
{
    if k >= bp.len() {
        tested
    } else if bp[k] > tested {
        spec_count_tested(bp, k + 1, tested + 1)
    } else {
        spec_count_tested(bp, k + 1, tested)
    }
}

pub open spec fn spec_count_tested_devices(bp: Seq<i32>) -> int
{
    spec_count_tested(bp, 0, 0)
}

impl Solution {
    pub fn count_tested_devices(battery_percentages: Vec<i32>) -> (result: i32)
        requires
            1 <= battery_percentages.len() <= 100,
            forall|i: int| 0 <= i < battery_percentages.len() ==> 0 <= #[trigger] battery_percentages[i] <= 100,
        ensures
            result as int == spec_count_tested_devices(battery_percentages@),
    {
        let n = battery_percentages.len();
        let mut tested = 0i32;
        let mut i = 0;
        while i < n
            decreases n - i,
        {
            if battery_percentages[i] > tested {
                tested = tested + 1;
            }
            i = i + 1;
        }
        tested
    }
}

}
