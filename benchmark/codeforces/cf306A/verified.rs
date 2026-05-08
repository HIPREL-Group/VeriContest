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
        while i < small_count
            invariant
                0 <= i <= small_count,
                small_count == m - r,
                r == n % m,
                q == n / m,
                1 <= m <= n <= 100,
                result.len() == i,
                forall|j: int| 0 <= j < result.len() ==> result[j] == q,
            decreases small_count - i,
        {
            result.push(q);
            i = i + 1;
        }
        let mut j: u32 = 0;
        while j < big_count
            invariant
                0 <= j <= big_count,
                big_count == r,
                small_count == m - r,
                r == n % m,
                q == n / m,
                1 <= m <= n <= 100,
                result.len() == small_count + j,
                forall|k: int| 0 <= k < small_count ==> result[k] == q,
                forall|k: int| small_count <= k < result.len() ==> result[k] == q + 1,
            decreases big_count - j,
        {
            result.push(q + 1);
            j = j + 1;
        }
        result
    }
}

}
