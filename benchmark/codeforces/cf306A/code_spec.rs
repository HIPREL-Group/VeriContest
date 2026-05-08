use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn distribute(n: u32, m: u32) -> (result: Vec<u32>)
        requires
            1 <= m <= n <= 100,
        ensures
            result.len() == m,
            forall|i: int| 0 <= i < result.len() ==>
                #[trigger] result[i] == (if i < (m as int) - (n as int % m as int) { (n / m) as u32 } else { (n / m + 1) as u32 }),
    {
        let q = n / m;
        let r = n % m;
        let big_count = r;
        let small_count = m - r;
        let mut result: Vec<u32> = Vec::new();
        let mut i: u32 = 0;
        while i < small_count {
            result.push(q);
            i = i + 1;
        }
        let mut j: u32 = 0;
        while j < big_count {
            result.push(q + 1);
            j = j + 1;
        }
        result
    }
}

}
