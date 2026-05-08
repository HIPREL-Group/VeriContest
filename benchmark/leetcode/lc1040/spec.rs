use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_sorted(s: Seq<i32>) -> bool {
    forall |i: int, j: int| 0 <= i < j < s.len() ==> s[i] < s[j]
}

pub open spec fn max_of(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

pub open spec fn min_of(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

pub open spec fn same_multiset(left: Seq<i32>, right: Seq<i32>) -> bool {
    left.len() == right.len() && left.to_multiset() =~= right.to_multiset()
}







pub open spec fn compute_max_moves(s: Seq<i32>) -> int {
    let n = s.len() as int;
    max_of(
        (s[n - 1] as int) - (s[1] as int) - n + 2,
        (s[n - 2] as int) - (s[0] as int) - n + 2,
    )
}





pub open spec fn left_bound(s: Seq<i32>, j: int, start: int) -> int
    decreases j - start + 1
{
    if start > j {
        j
    } else if (s[j] as int) - (s[start] as int) < (s.len() as int) {
        start
    } else {
        left_bound(s, j, start + 1)
    }
}





pub open spec fn cost_at(s: Seq<i32>, j: int) -> int {
    let n = s.len() as int;
    let i = left_bound(s, j, 0);
    let count = j - i + 1;
    if count == n - 1 && (s[j] as int) - (s[i] as int) == n - 2 {
        2int
    } else {
        n - count
    }
}









pub open spec fn min_cost(s: Seq<i32>, j: int) -> int
    decreases j + 1
{
    if j < 0 {
        s.len() as int
    } else {
        min_of(cost_at(s, j), min_cost(s, j - 1))
    }
}

impl Solution {
    pub fn num_moves_stones_ii(stones: Vec<i32>) -> (result: Vec<i32>)
        requires
            stones@.len() >= 3,
            stones@.len() <= 10000,
            forall |i: int, j: int| 0 <= i < j < stones@.len() ==>
                stones@[i] != stones@[j],
            forall |i: int| 0 <= i < stones@.len() ==>
                1 <= #[trigger] stones[i] <= 1_000_000_000i32,
        ensures
            result@.len() == 2,
            exists |sorted_s: Seq<i32>|
                is_sorted(sorted_s)
                && same_multiset(sorted_s, stones@)
                && result[0] as int == min_cost(sorted_s, sorted_s.len() as int - 1)
                && result[1] as int == compute_max_moves(sorted_s),
    {
    }
}

}
