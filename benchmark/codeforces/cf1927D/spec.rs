use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn all_equal_range(a: Seq<i64>, l: int, r: int) -> bool
        recommends
            0 <= l <= r < a.len(),
    {
        forall|i: int, j: int| l <= i && i < j && j <= r ==> a[i] == a[j]
    }

    pub open spec fn valid_query_answer(a: Seq<i64>, q: (usize, usize), out: (i32, i32)) -> bool {
        let l = q.0 as int;
        let r = q.1 as int;
        let x = out.0 as int;
        let y = out.1 as int;
        ((x == -1 && y == -1) && Self::all_equal_range(a, l - 1, r - 1))
        ||
        (l <= x < y <= r && a[x - 1] != a[y - 1])
    }

    pub fn find_different_ones(a: Vec<i64>, queries: Vec<(usize, usize)>) -> (res: Vec<(i32, i32)>)
        requires
            2 <= a.len() <= 200000,
            forall|i: int| 0 <= i < a.len() as int ==> 1 <= #[trigger] a[i] <= 1000000,
            forall|k: int| 0 <= k < queries.len() as int ==> 1 <= #[trigger] queries[k].0 < queries[k].1 <= a.len(),
        ensures
            res.len() == queries.len(),
            forall|k: int| 0 <= k < queries.len() as int ==> Self::valid_query_answer(a@, queries[k], #[trigger] res[k]),
    {
    }
}

}
