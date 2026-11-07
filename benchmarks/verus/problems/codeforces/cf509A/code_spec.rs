use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn table_value(n: int, i: int, j: int) -> int
    decreases i + j,
{
    if i < 0 || j < 0 || i >= n || j >= n {
        0int
    } else if i == 0 || j == 0 {
        1int
    } else {
        table_value(n, i - 1, j) + table_value(n, i, j - 1)
    }
}

impl Solution {
    pub fn max_in_table(n: u32) -> (result: u32)
        requires
            1 <= n <= 10,
        ensures
            result as int == table_value(n as int, (n - 1) as int, (n - 1) as int),
    {
        let nu: usize = n as usize;
        let mut row: Vec<u32> = Vec::new();
        let mut k: usize = 0;
        while k < nu {
            row.push(1u32);
            k = k + 1;
        }
        let mut i: usize = 1;
        while i < nu {
            let mut j: usize = 1;
            while j < nu {
                let v: u32 = row[j] + row[j - 1];
                row.set(j, v);
                j = j + 1;
            }
            i = i + 1;
        }
        row[nu - 1]
    }
}

}
