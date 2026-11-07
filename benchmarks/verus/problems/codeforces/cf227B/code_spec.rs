use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn value_occurs(permutation: Seq<i32>, value: int) -> bool {
    exists|pos: int| 0 <= pos < permutation.len() && permutation[pos] == value
}

pub open spec fn all_values_occur(permutation: Seq<i32>) -> bool {
    forall|value: int| 1 <= value <= permutation.len() ==> #[trigger] value_occurs(permutation, value)
}

pub open spec fn is_valid_permutation(permutation: Seq<i32>) -> bool {
    1 <= permutation.len() <= 100_000
        && forall|i: int| 0 <= i < permutation.len() ==> 1 <= #[trigger] permutation[i] <= permutation.len()
        && forall|i: int, j: int| 0 <= i < j < permutation.len() ==> permutation[i] != permutation[j]
        && all_values_occur(permutation)
}

pub open spec fn are_valid_queries(queries: Seq<i32>, n: int) -> bool {
    1 <= queries.len() <= 100_000
        && forall|i: int| 0 <= i < queries.len() ==> 1 <= #[trigger] queries[i] <= n
}

pub open spec fn position_of(permutation: Seq<i32>, value: int) -> int
    recommends
        is_valid_permutation(permutation),
        1 <= value <= permutation.len(),
{
    choose|pos: int| 0 <= pos < permutation.len() && permutation[pos] == value
}

pub open spec fn total_vasya(permutation: Seq<i32>, queries: Seq<i32>, k: int) -> int
    recommends
        is_valid_permutation(permutation),
        are_valid_queries(queries, permutation.len() as int),
        0 <= k <= queries.len(),
    decreases k,
{
    if k <= 0 {
        0
    } else {
        total_vasya(permutation, queries, k - 1) + position_of(permutation, queries[k - 1] as int) + 1
    }
}

pub open spec fn total_petya(permutation: Seq<i32>, queries: Seq<i32>, k: int) -> int
    recommends
        is_valid_permutation(permutation),
        are_valid_queries(queries, permutation.len() as int),
        0 <= k <= queries.len(),
    decreases k,
{
    if k <= 0 {
        0
    } else {
        total_petya(permutation, queries, k - 1) + permutation.len() - position_of(permutation, queries[k - 1] as int)
    }
}

impl Solution {
    pub fn effective_approach(permutation: Vec<i32>, queries: Vec<i32>) -> (result: (i64, i64))
        requires
            is_valid_permutation(permutation@),
            all_values_occur(permutation@),
            are_valid_queries(queries@, permutation.len() as int),
        ensures
            result.0 as int == total_vasya(permutation@, queries@, queries.len() as int),
            result.1 as int == total_petya(permutation@, queries@, queries.len() as int),
    {
        let n = permutation.len();
        let mut positions = Vec::new();
        let mut t = 0usize;
        while t <= n {
            positions.push(0i64);
            t += 1;
        }
        let mut i = 0usize;
        while i < n {
            let value = permutation[i] as usize;
            positions.set(value, i as i64 + 1);
            i += 1;
        }
        let mut vasya = 0i64;
        let mut petya = 0i64;
        let mut j = 0usize;
        while j < queries.len() {
            let value = queries[j] as usize;
            let p = positions[value];
            vasya += p;
            petya += n as i64 - p + 1;
            j += 1;
        }
        (vasya, petya)
    }
}

}
