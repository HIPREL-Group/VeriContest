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
            30 >= last.len() >= 1,
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

    pub fn generate(num_rows: i32) -> (triangle: Vec<Vec<i32>>)
        requires
            1 <= num_rows <= 30,
        ensures
            triangle.len() == num_rows as int,
            forall|n: int|
                0 <= n < triangle.len() ==> #[trigger] triangle[n]@ =~= Self::pascals_triangle(
                    n as nat,
                ),
    {
        let num_rows = num_rows as usize;
        let mut triangle = Vec::with_capacity(num_rows);
        triangle.push(vec![1]);
        while triangle.len() < num_rows {
            let last_n = triangle.len() - 1;
            triangle.push(Self::gen_next(&triangle[last_n]));
        }
        triangle
    }
}

} 
