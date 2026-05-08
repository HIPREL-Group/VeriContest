use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_ones_spec(n: int) -> int
    decreases n
{
    if n <= 0 {
        0
    } else {
        (n % 2) + count_ones_spec(n / 2)
    }
}

pub open spec fn bit_le(a: int, b: int) -> bool {
    count_ones_spec(a) < count_ones_spec(b)
    || (count_ones_spec(a) == count_ones_spec(b) && a <= b)
}

pub open spec fn sorted_by_bits(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> bit_le(s[i] as int, s[j] as int)
}

pub open spec fn count_occ(s: Seq<i32>, v: i32) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        (if s[0] == v { 1int } else { 0int }) + count_occ(s.subrange(1, s.len() as int), v)
    }
}

pub open spec fn is_permutation(a: Seq<i32>, b: Seq<i32>) -> bool {
    a.len() == b.len() && forall|v: i32| count_occ(a, v) == count_occ(b, v)
}

impl Solution {
    pub fn sort_by_bits(arr: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= arr.len() <= 500,
            forall|i: int| 0 <= i < arr.len() ==> 0 <= #[trigger] arr[i] <= 10000,
        ensures
            result.len() == arr.len(),
            sorted_by_bits(result@),
            is_permutation(arr@, result@),
    {
    }
}

}
