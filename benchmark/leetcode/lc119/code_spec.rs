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

    pub fn gen_next(last: &Vec<i32>) -> (ret: Vec<i32>)
        requires
            33 >= last.len() >= 1,
            last@ =~= Self::pascals_triangle((last.len() - 1) as nat),
        ensures
            ret@ =~= Self::pascals_triangle(last.len() as nat),
    {
        let mut i = 1;
        let mut ret = Vec::with_capacity(last.len() + 1);
        ret.push(last[0]);
        while i < last.len() {
            ret.push(last[i - 1] + last[i]);
            i += 1;
        }
        ret.push(last[last.len() - 1]);
        ret
    }

    pub fn get_row(row_index: i32) -> (row: Vec<i32>)
        requires
            0 <= row_index <= 33,
        ensures
            row@ =~= Self::pascals_triangle(row_index as nat),
    {
        let mut i = 0;
        let mut row = vec![1];
        while i != row_index {
            row = Self::gen_next(&row);
            i += 1;
        }
        row
    }
}

} 
