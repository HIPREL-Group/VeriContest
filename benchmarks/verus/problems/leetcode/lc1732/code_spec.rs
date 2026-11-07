use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn altitude_at(gain: Seq<i32>, k: int) -> int
        decreases k
    {
        if k <= 0 {
            0
        } else {
            Self::altitude_at(gain, k - 1) + gain[k - 1] as int
        }
    }
    
    pub fn largest_altitude(gain: Vec<i32>) -> (result: i32)
        requires
            1 <= gain.len() <= 100,
            forall|i: int| 0 <= i < gain.len() ==> -100 <= #[trigger] gain[i] <= 100,
        ensures
            exists|k: int| 0 <= k <= gain.len() && result == Self::altitude_at(gain@, k),
            forall|k: int| 0 <= k <= gain.len() ==> Self::altitude_at(gain@, k) <= result,
    {
        let mut max_alt: i32 = 0;
        let mut cur: i32 = 0;
        let n = gain.len();
        let mut i: usize = 0;
        while i < n
        {
            cur = cur + gain[i];
            if cur > max_alt {
                max_alt = cur;
            }
            i += 1;
        }
        max_alt
    }
}

}
