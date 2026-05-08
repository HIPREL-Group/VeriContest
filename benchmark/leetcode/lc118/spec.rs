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
    }
}

} 
