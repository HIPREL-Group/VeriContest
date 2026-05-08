use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn has_val(s: Seq<i32>, v: i32) -> bool {
        exists|i: int| 0 <= i < s.len() && s[i] == v
    }

    pub open spec fn num_distinct(s: Seq<i32>) -> int
        decreases s.len(),
    {
        if s.len() == 0 {
            0int
        } else {
            let rest = Self::num_distinct(s.drop_last());
            if Self::has_val(s.drop_last(), s.last()) {
                rest
            } else {
                rest + 1
            }
        }
    }

    pub fn distribute_candies(candy_type: Vec<i32>) -> (res: i32)
        requires
            candy_type.len() % 2 == 0,
            2 <= candy_type.len() <= 10_000,
            forall|i: int| 0 <= i < candy_type.len() ==>
                -100_000 <= #[trigger] candy_type[i] <= 100_000,
        ensures
            res == if Self::num_distinct(candy_type@) <= candy_type.len() / 2 {
                Self::num_distinct(candy_type@) as i32
            } else {
                (candy_type.len() / 2) as i32
            },
    {
        let mut seen: Vec<bool> = Vec::new();
        let mut fill_idx = 0usize;
        while fill_idx < 200001usize {
            seen.push(false);
            fill_idx += 1;
        }
        let mut distinct = 0i32;
        let n = candy_type.len();
        let mut i = 0usize;
        while i < n {
            let ci = candy_type[i];
            let offset = (ci as i64 + 100_000i64) as usize;
            if !seen[offset] {
                seen.set(offset, true);
                distinct += 1;
            }
            i += 1;
        }
        let half = (n / 2) as i32;
        if distinct <= half { distinct } else { half }
    }
}

} 
