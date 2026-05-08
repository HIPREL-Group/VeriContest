use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn decode(encoded: Vec<i32>, first: i32) -> (result: Vec<i32>)
        requires
            encoded.len() <= 100000,
            forall |i: int| 0 <= i && i < encoded.len() ==> 0 <= encoded[i] && encoded[i] <= 100000,
            0 <= first && first <= 100000,
        ensures
            result.len() == encoded.len() + 1,
            result[0] == first,
            forall |i: int| 0 <= i && i < encoded.len() ==> result[i] ^ result[i + 1] == encoded[i],
    {
        let mut ans = Vec::new();
        ans.push(first);
        let mut i = 0;
        while i < encoded.len()
            invariant
                ans.len() == i + 1,
                ans[0] == first,
                i <= encoded.len(),
                forall |j: int| 0 <= j && j < i ==> ans[j] ^ ans[j + 1] == encoded[j],
            decreases encoded.len() - i,
        {
            let next = ans[i] ^ encoded[i];
            ans.push(next);
            proof {
                let idx = i as int;
                let a = ans@[idx];
                let b = encoded@[idx];
                assert(a ^ (a ^ b) == b) by(bit_vector);
            }
            i = i + 1;
        }
        ans
    }
}

}
