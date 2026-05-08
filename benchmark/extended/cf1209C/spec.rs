use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn spec_c1_values(d: Seq<i32>, c: Seq<i32>, n: int) -> Seq<i32>
    decreases n,
{
    if n <= 0 {
        seq![]
    } else {
        let rest = spec_c1_values(d, c, n - 1);
        if c[n - 1] == 1 {
            rest + seq![d[n - 1]]
        } else {
            rest
        }
    }
}

pub open spec fn spec_c2_values(d: Seq<i32>, c: Seq<i32>, n: int) -> Seq<i32>
    decreases n,
{
    if n <= 0 {
        seq![]
    } else {
        let rest = spec_c2_values(d, c, n - 1);
        if c[n - 1] == 2 {
            rest + seq![d[n - 1]]
        } else {
            rest
        }
    }
}

pub open spec fn spec_merged_digits(d: Seq<i32>, c: Seq<i32>, n: int) -> Seq<i32> {
    spec_c1_values(d, c, n) + spec_c2_values(d, c, n)
}

pub open spec fn spec_adjacent_nondecreasing(s: Seq<i32>) -> bool {
    forall|i: int| #![trigger s[i]] 0 <= i < s.len() - 1 ==> s[i] <= s[i + 1]
}

pub open spec fn spec_valid_coloring(d: Seq<i32>, c: Seq<i32>) -> bool {
    d.len() == c.len()
        && (forall|i: int| 0 <= i < d.len() ==> #[trigger] c[i] == 1 || c[i] == 2)
        && spec_adjacent_nondecreasing(spec_merged_digits(d, c, d.len() as int))
}

pub struct Solution;

impl Solution {
    pub fn paint_digits(digits: Vec<i32>) -> (res: Vec<i32>)
        requires
            1 <= digits.len() <= 200_000,
            forall|i: int|
                #![trigger digits[i]]
                0 <= i < digits.len() as int ==> 0 <= #[trigger] digits[i] <= 9,
        ensures
            res.len() == 0 || res.len() == digits.len(),
            res.len() == digits.len() ==> spec_valid_coloring(digits@, res@),
    {
    }
}

}
