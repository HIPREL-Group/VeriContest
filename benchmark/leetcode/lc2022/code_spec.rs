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
        if original.len() != (m as usize) * (n as usize) {
            return Vec::new();
        }

        let mut result: Vec<Vec<i32>> = Vec::new();
        let mut ri: usize = 0;
        while ri < m as usize
        {
            let mut row: Vec<i32> = Vec::new();
            let mut ci: usize = 0;
            while ci < n as usize
            {
                row.push(0i32);
                ci += 1;
            }
            result.push(row);
            ri += 1;
        }

        let mut i: usize = 0;
        while i < m as usize
        {
            let mut j: usize = 0;
            while j < n as usize
            {
                let idx: usize = i * n as usize + j;
                let val = original[idx];
                let mut row = result[i].clone();
                row.set(j, val);
                result.set(i, row);
                j += 1;
            }
            i += 1;
        }

        result
    }
}

}