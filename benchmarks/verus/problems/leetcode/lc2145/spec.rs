use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn prefix_sum(differences: Seq<i32>, end: int) -> int
        recommends
            0 <= end <= differences.len(),
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::prefix_sum(differences, end - 1) + differences[end - 1] as int
        }
    }

    pub open spec fn min_prefix(differences: Seq<i32>, upto: int) -> int
        recommends
            0 <= upto <= differences.len(),
        decreases upto,
    {
        if upto <= 0 {
            0
        } else {
            let prev = Self::min_prefix(differences, upto - 1);
            let cur = Self::prefix_sum(differences, upto);
            if cur < prev {
                cur
            } else {
                prev
            }
        }
    }

    pub open spec fn max_prefix(differences: Seq<i32>, upto: int) -> int
        recommends
            0 <= upto <= differences.len(),
        decreases upto,
    {
        if upto <= 0 {
            0
        } else {
            let prev = Self::max_prefix(differences, upto - 1);
            let cur = Self::prefix_sum(differences, upto);
            if prev < cur {
                cur
            } else {
                prev
            }
        }
    }

    pub open spec fn number_of_arrays_spec(differences: Seq<i32>, lower: int, upper: int) -> int
        recommends
            lower <= upper,
    {
        let min_p = Self::min_prefix(differences, differences.len() as int);
        let max_p = Self::max_prefix(differences, differences.len() as int);
        let width = upper - lower;
        let span = max_p - min_p;
        if width < span {
            0
        } else {
            width - span + 1
        }
    }

    pub fn number_of_arrays(differences: Vec<i32>, lower: i32, upper: i32) -> (result: i32)
        requires
            1 <= differences.len() <= 100_000,
            -100_000 <= lower <= upper <= 100_000,
            forall |i: int| 0 <= i < differences.len() ==> -100_000 <= #[trigger] differences[i] <= 100_000,
        ensures
            0 <= result,
            result as int == Self::number_of_arrays_spec(differences@, lower as int, upper as int),
    {
    }
}

}
