use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn find_array(pref: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= pref.len() <= 100_000,
            forall |i: int| 0 <= i < pref.len() ==> 0 <= #[trigger] pref[i] <= 1_000_000,
        ensures
            result.len() == pref.len(),
            result[0] == pref[0],
            forall |i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i],
            forall |i: int| 1 <= i < pref.len() ==>
                pref[i] == (#[trigger] pref[i - 1]) ^ result[i],
    {
        let n = pref.len();
        let mut result: Vec<i32> = Vec::new();
        result.push(pref[0]);
        let mut i: usize = 1;
        while i < n
            invariant
                n == pref.len(),
                1 <= n <= 100_000,
                1 <= i <= n,
                result.len() == i,
                result[0] == pref[0],
                forall |k: int| 0 <= k < pref.len() ==> 0 <= #[trigger] pref[k] <= 1_000_000,
                forall |k: int| 0 <= k < i as int ==> 0 <= #[trigger] result[k],
                forall |k: int| 1 <= k < i as int ==>
                    pref[k] == (#[trigger] pref[k - 1]) ^ result[k],
            decreases n - i,
        {
            let a = pref[i];
            let b = pref[i - 1];
            let val = a ^ b;
            proof {
                assert(0 <= a ^ b) by (bit_vector)
                    requires
                        0 <= a,
                        0 <= b,
                ;
                assert(b ^ val == a) by (bit_vector)
                    requires
                        val == a ^ b,
                ;
            }
            result.push(val);
            i = i + 1;
        }
        result
    }
}

}
