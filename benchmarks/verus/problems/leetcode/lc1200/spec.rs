use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn abs_diff(a: int, b: int) -> int {
    if a >= b { a - b } else { b - a }
}

pub open spec fn seq_contains(s: Seq<i32>, v: i32) -> bool {
    exists |i: int| 0 <= i < s.len() && s[i] == v
}

pub open spec fn consec_diff(s: Seq<i32>, k: int) -> int
    recommends 0 <= k < s.len() - 1,
{
    s[k + 1] - s[k]
}

pub open spec fn has_pair(res: Seq<Vec<i32>>, a: i32, b: i32) -> bool {
    exists |k: int| 0 <= k < res.len() && res[k][0] == a && res[k][1] == b
}

impl Solution {
    pub fn minimum_abs_difference(arr: Vec<i32>) -> (res: Vec<Vec<i32>>)
        requires
            2 <= arr.len() <= 100_000,
            forall |i: int| 0 <= i < arr.len() ==> -1_000_000 <= #[trigger] arr[i] <= 1_000_000,
            forall |i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] != arr[j],
        ensures
            res.len() >= 1,
            forall |i: int| 0 <= i < res.len() ==> (#[trigger] res[i]).len() == 2,
            forall |i: int| 0 <= i < res.len() ==> (#[trigger] res[i])[0] < res[i][1],
            forall |i: int| 0 <= i < res.len() ==>
                #[trigger] seq_contains(arr@, res[i][0]),
            forall |i: int| 0 <= i < res.len() ==>
                #[trigger] seq_contains(arr@, res[i][1]),
            forall |i: int| 0 <= i < res.len() ==>
                ((#[trigger] res[i])[1] - res[i][0]) == (res[0][1] - res[0][0]),
            forall |p: int, q: int| 0 <= p < q < arr.len() ==>
                #[trigger] abs_diff(arr[p] as int, arr[q] as int) >= (res[0][1] - res[0][0]) as int,
            forall |i: int, j: int| 0 <= i < j < res.len() ==>
                (#[trigger] res[i])[0] < (#[trigger] res[j])[0],
            forall |p: int, q: int| 0 <= p < arr.len() && 0 <= q < arr.len()
                && arr[p] < arr[q]
                && #[trigger] abs_diff(arr[p] as int, arr[q] as int) == (res[0][1] - res[0][0]) as int
                ==> has_pair(res@, arr[p], arr[q]),
    {
    }
}

}
