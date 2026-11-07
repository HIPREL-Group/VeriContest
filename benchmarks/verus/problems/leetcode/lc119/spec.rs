use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn pascals_triangle(n: nat) -> Seq<i32>
        decreases n,
    {
        if n == 0 {
            seq![1]
        } else {
            let last = Self::pascals_triangle((n - 1) as nat);
            Seq::new(
                last.len() + 1,
                |i: int|
                    {
                        if i == 0 {
                            last[i]
                        } else if i == last.len() {
                            last[i - 1]
                        } else {
                            (last[i - 1] + last[i]) as i32
                        }
                    },
            )
        }
    }

    pub fn get_row(row_index: i32) -> (row: Vec<i32>)
        requires
            0 <= row_index <= 33,
        ensures
            row@ =~= Self::pascals_triangle(row_index as nat),
    {
    }
}

} 
