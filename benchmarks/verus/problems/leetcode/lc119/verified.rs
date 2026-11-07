use vstd::arithmetic::power2::{
    lemma2_to64, lemma2_to64_rest, lemma_pow2_strictly_increases, lemma_pow2_unfold, pow2,
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

    pub proof fn lemma_pascal9()
        ensures
            Self::pascals_triangle(9) =~= seq![1, 9, 36, 84, 126, 126, 84, 36, 9, 1],
    {
        assert(Self::pascals_triangle(9) =~= seq![1, 9, 36, 84, 126, 126, 84, 36, 9, 1])
            by (compute_only);
    }

    pub proof fn lemma_pascal_bounds(n: nat)
        requires
            n <= 33,
        ensures
            forall|i: int| 0 <= i <= n ==> Self::pascals_triangle(n)[i] > 0,
            forall|i: int|
                0 <= i <= n && n > 0 ==> Self::pascals_triangle(n)[i] <= pow2((n - 1) as nat),
            forall|i: int|
                0 <= i <= n && n > 8 ==> Self::pascals_triangle(n)[i] < pow2((n - 2) as nat),
        decreases n,
    {
        lemma2_to64();
        if n == 9 {
            Self::lemma_pascal9();
        }
        if n != 0 {
            let last = Self::pascals_triangle((n - 1) as nat);
            Self::lemma_pascal_bounds((n - 1) as nat);
            Self::lemma_pascal_len(n);
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
        while i < last.len()
            invariant
                1 <= i <= last.len(),
                33 >= last.len() >= 1,
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

    pub fn get_row(row_index: i32) -> (row: Vec<i32>)
        requires
            0 <= row_index <= 33,
        ensures
            row@ =~= Self::pascals_triangle(row_index as nat),
    {
        let mut i = 0;
        let mut row = vec![1];
        while i != row_index
            invariant
                0 <= i <= row_index <= 33,
                row@ =~= Self::pascals_triangle(i as nat),
            decreases row_index - i,
        {
            proof {
                Self::lemma_pascal_len(i as nat);
            }
            row = Self::gen_next(&row);
            i += 1;
        }
        row
    }
}

} 
