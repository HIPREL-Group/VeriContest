use vstd::arithmetic::power2::{
    lemma2_to64, lemma_pow2_strictly_increases, lemma_pow2_unfold, pow2,
};
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

    pub proof fn lemma_pascal_len(n: nat)
        ensures
            Self::pascals_triangle(n).len() == n + 1,
        decreases n,
    {
        if n != 0 {
            Self::lemma_pascal_len((n - 1) as nat);
        }
    }

    pub proof fn lemma_pascal_bounds(n: nat)
        requires
            n <= 30,
        ensures
            forall|i: int| 0 <= i <= n ==> Self::pascals_triangle(n)[i] > 0,
            forall|i: int|
                0 <= i <= n && n > 0 ==> Self::pascals_triangle(n)[i] <= pow2((n - 1) as nat),
        decreases n,
    {
        lemma2_to64();
        if n != 0 {
            let last = Self::pascals_triangle((n - 1) as nat);
            Self::lemma_pascal_bounds((n - 1) as nat);
            Self::lemma_pascal_len(n);
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
        while i < last.len()
            invariant
                1 <= i <= last.len(),
                30 >= last.len() >= 1,
                i == ret.len(),
                last@ =~= Self::pascals_triangle((last.len() - 1) as nat),
                ret@ =~= Self::pascals_triangle(last.len() as nat).take(ret.len() as int),
            decreases last.len() - i,
        {
            proof {
                Self::lemma_pascal_bounds((last.len() - 1) as nat);
                lemma2_to64();
            }
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
        while triangle.len() < num_rows
            invariant
                triangle.len() >= 1,
                1 <= num_rows <= 30,
                triangle.len() <= num_rows,
                forall|n: int|
                    0 <= n < triangle.len() ==> #[trigger] triangle[n]@ =~= Self::pascals_triangle(
                        n as nat,
                    ),
            decreases num_rows - triangle.len(),
        {
            let last_n = triangle.len() - 1;
            proof {
                Self::lemma_pascal_len(last_n as nat);
            }
            triangle.push(Self::gen_next(&triangle[last_n]));
        }
        triangle
    }
}

} 
