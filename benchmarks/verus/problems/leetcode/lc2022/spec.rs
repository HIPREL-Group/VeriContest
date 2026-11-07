use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn construct2_d_array(original: Vec<i32>, m: i32, n: i32) -> (res: Vec<Vec<i32>>)
        requires
            1 <= original.len() <= 50_000,
            1 <= m <= 40_000,
            1 <= n <= 40_000,
            m * n <= usize::MAX,
            forall |i: int| 0 <= i < original.len() ==> 1 <= #[trigger] original[i] <= 100_000,
        ensures
            ({
                if original.len() != m as usize * n as usize {
                    res@ =~= Seq::<Vec<i32>>::empty()
                } else {
                    res.len() == m as int
                    && (forall |i: int| 0 <= i < m ==> #[trigger] res[i].len() == n as int)
                    && (forall |i: int, j: int| 0 <= i < m && 0 <= j < n ==>
                        res[i][j] == original[i * n as int + j])
                }
            }),
    {
        
    }
}

}