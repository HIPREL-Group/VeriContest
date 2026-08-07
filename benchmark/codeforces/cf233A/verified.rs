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
                1 <= #[trigger] result.unwrap()[i] <= n),
            result.is_some() ==> (forall|i: int| 0 <= i < n ==>
                #[trigger] result.unwrap()[(result.unwrap()[i] - 1) as int] == (i + 1) as u32),
            result.is_some() ==> (forall|i: int| 0 <= i < n ==>
                #[trigger] result.unwrap()[i] != (i + 1) as u32),
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
        proof {
            assert forall|k: int| 0 <= k < n implies 1 <= #[trigger] result[k] <= n by {
                if k % 2 == 0 {
                    assert(result[k] == (k + 2) as u32);
                } else {
                    assert(result[k] == k as u32);
                }
            };
            assert forall|k: int| 0 <= k < n implies
                #[trigger] result[(result[k] - 1) as int] == (k + 1) as u32 by {
                if k % 2 == 0 {
                    assert(result[k] == (k + 2) as u32);
                    assert((result[k] - 1) as int == k + 1);
                    assert((k + 1) % 2 != 0);
                    assert(result[k + 1] == (k + 1) as u32);
                } else {
                    assert(result[k] == k as u32);
                    assert((result[k] - 1) as int == k - 1);
                    assert((k - 1) % 2 == 0);
                    assert(result[k - 1] == (k - 1 + 2) as u32);
                }
            };
            assert forall|k: int| 0 <= k < n implies #[trigger] result[k] != (k + 1) as u32 by {
                if k % 2 == 0 {
                    assert(result[k] == (k + 2) as u32);
                } else {
                    assert(result[k] == k as u32);
                }
            };
        }
        Some(result)
    }
}

}
