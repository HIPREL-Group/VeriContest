use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn perfect_permutation(n: u32) -> (result: Option<Vec<u32>>)
        requires
            1 <= n <= 100,
        ensures
            result.is_some() <==> (n % 2 == 0),
            result.is_some() ==> result.unwrap().len() == n,
            result.is_some() ==> (forall|i: int| 0 <= i < n ==>
                #[trigger] result.unwrap()[i] == (if i % 2 == 0 { (i + 2) as u32 } else { i as u32 })),
    {
        if n % 2 != 0 {
            return None;
        }
        let mut result: Vec<u32> = Vec::new();
        let mut i: u32 = 0;
        while i < n
            invariant
                0 <= i <= n,
                1 <= n <= 100,
                n % 2 == 0,
                result.len() == i,
                forall|k: int| 0 <= k < result.len() ==>
                    #[trigger] result[k] == (if k % 2 == 0 { (k + 2) as u32 } else { k as u32 }),
            decreases n - i,
        {
            if i % 2 == 0 {
                result.push(i + 2);
            } else {
                result.push(i);
            }
            i = i + 1;
        }
        Some(result)
    }
}

}
