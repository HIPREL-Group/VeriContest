use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn popcount(x: int) -> int
        decreases x,
    {
        if x <= 0 { 0 } else { (x % 2) + Self::popcount(x / 2) }
    }

    pub fn count_bits(n: i32) -> (res: Vec<i32>)
        requires
            0 <= n <= 100000,
        ensures
            res.len() == n + 1,
            forall|i: int| 0 <= i < res.len() ==> #[trigger] res[i] as int == Self::popcount(i),
    {
        let n_usize = n as usize;
        let mut ans: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k <= n_usize {
            ans.push(0);
            k += 1;
        }
        let mut i: usize = 1;
        while i <= n_usize {
            let half: usize = i / 2;
            let bit: usize = i % 2;
            let v = ans[half] + (bit as i32);
            ans.set(i, v);
            i += 1;
        }
        ans
    }
}

}
