use vstd::prelude::*;

fn main() {}

verus! {
pub struct Solution;

impl Solution {
    pub fn max_distance(colors: Vec<i32>) -> (result: i32)
        requires
            2 <= colors.len() <= 100,
            forall |i: int| 0 <= i < colors.len() ==> 0 <= #[trigger] colors[i] <= 100,
            exists |i: int, j: int| 0 <= i < j < colors.len() && colors[i] != colors[j],
        ensures
            result >= 0,
            exists |i: int, j: int| 0 <= i < j < colors.len() && colors[i] != colors[j] && #[trigger] (j - i) == result,
            forall |i: int, j: int| 0 <= i < j < colors.len() ==> colors[i] == colors[j] || #[trigger] (j - i) <= result,
    {
        let n = colors.len();
        let mut result: i32 = 0;
        let mut i = 0;
        while i < n
        {
            let mut j = n - 1;
            while j > i
            {
                let dist = (j - i) as i32;
                if colors[i] != colors[j] && dist > result {
                    result = dist;
                }
                j -= 1;
            }
            i += 1;
        }
        result
    }
}
}
