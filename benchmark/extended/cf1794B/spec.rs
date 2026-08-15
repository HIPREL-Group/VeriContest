use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn seq_elements_positive(s: Seq<i32>) -> bool {
    forall|i: int|
        #![trigger s[i]]
        0 <= i && i < s.len() ==> s[i] >= 1 && s[i] <= 1_000_000_000
}

pub open spec fn seq_neighbors_not_dividing(s: Seq<i32>) -> bool {
    forall|i: int|
        #![trigger s[i]]
        0 <= i && i < s.len() - 1 ==> s[i] >= 1 && s[i + 1] >= 1 && (s[i + 1] as int) % (s[i] as int) != 0
}

pub open spec fn seq_pointwise_ge(orig: Seq<i32>, res: Seq<i32>) -> bool {
    orig.len() == res.len()
        && (forall|i: int|
            #![trigger res[i]]
            0 <= i && i < orig.len() ==> res[i] >= orig[i])
}

pub open spec fn seq_increase_sum(orig: Seq<i32>, res: Seq<i32>, end: int) -> int
    decreases end,
{
    if end <= 0 {
        0
    } else {
        seq_increase_sum(orig, res, end - 1) + ((res[end - 1] as int) - (orig[end - 1] as int))
    }
}

pub open spec fn seq_total_increase_bounded(orig: Seq<i32>, res: Seq<i32>) -> bool {
    orig.len() == res.len()
        && seq_increase_sum(orig, res, orig.len() as int) <= 2 * orig.len()
}

pub struct Solution;

impl Solution {
    pub fn not_dividing_array(a: Vec<i32>) -> (res: Vec<i32>)
        requires
            1 <= a.len() <= 10000,
            seq_elements_positive(a@),
        ensures
            res@.len() == a@.len(),
            seq_neighbors_not_dividing(res@),
            seq_pointwise_ge(a@, res@),
            seq_total_increase_bounded(a@, res@),
    {
    }
}

}
