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

proof fn lemma_position_of_properties(permutation: Seq<i32>, value: int)
    requires
        is_valid_permutation(permutation),
        all_values_occur(permutation),
        1 <= value <= permutation.len(),
    ensures
        0 <= position_of(permutation, value) < permutation.len(),
        permutation[position_of(permutation, value)] == value,
        forall|pos: int| 0 <= pos < permutation.len() && permutation[pos] == value ==> pos == position_of(permutation, value),
{
    assert(value_occurs(permutation, value)) by {
        reveal_with_fuel(all_values_occur, 1);
        assert(1 <= value <= permutation.len());
    }
    assert(exists|pos: int| 0 <= pos < permutation.len() && permutation[pos] == value) by {
        assert(value_occurs(permutation, value));
    }
    let chosen = position_of(permutation, value);
    assert(0 <= chosen < permutation.len());
    assert(permutation[chosen] == value);
    assert forall|pos: int| 0 <= pos < permutation.len() && permutation[pos] == value implies pos == chosen by {
        if pos < chosen {
            assert(permutation[pos] != permutation[chosen]);
        } else if chosen < pos {
            assert(permutation[chosen] != permutation[pos]);
        }
    }
}

proof fn lemma_total_bounds(permutation: Seq<i32>, queries: Seq<i32>, k: int)
    requires
        is_valid_permutation(permutation),
        all_values_occur(permutation),
        are_valid_queries(queries, permutation.len() as int),
        0 <= k <= queries.len(),
    ensures
        0 <= total_vasya(permutation, queries, k) <= k * 100_000,
        0 <= total_petya(permutation, queries, k) <= k * 100_000,
    decreases k,
{
    if k > 0 {
        lemma_total_bounds(permutation, queries, k - 1);
        lemma_position_of_properties(permutation, queries[k - 1] as int);
        lemma_total_vasya_step(permutation, queries, k - 1);
        lemma_total_petya_step(permutation, queries, k - 1);
        assert(0 <= position_of(permutation, queries[k - 1] as int) + 1 <= 100_000);
        assert(0 <= permutation.len() - position_of(permutation, queries[k - 1] as int) <= 100_000);
    }
}

proof fn lemma_total_vasya_step(permutation: Seq<i32>, queries: Seq<i32>, k: int)
    requires
        is_valid_permutation(permutation),
        all_values_occur(permutation),
        are_valid_queries(queries, permutation.len() as int),
        0 <= k < queries.len(),
    ensures
        total_vasya(permutation, queries, k + 1) == total_vasya(permutation, queries, k) + position_of(permutation, queries[k] as int) + 1,
{
    reveal_with_fuel(total_vasya, 2);
}

proof fn lemma_total_petya_step(permutation: Seq<i32>, queries: Seq<i32>, k: int)
    requires
        is_valid_permutation(permutation),
        all_values_occur(permutation),
        are_valid_queries(queries, permutation.len() as int),
        0 <= k < queries.len(),
    ensures
        total_petya(permutation, queries, k + 1) == total_petya(permutation, queries, k) + permutation.len() - position_of(permutation, queries[k] as int),
{
    reveal_with_fuel(total_petya, 2);
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
        while t <= n
            invariant
                n == permutation.len(),
                is_valid_permutation(permutation@),
                all_values_occur(permutation@),
                are_valid_queries(queries@, permutation.len() as int),
                0 <= t <= n + 1,
                positions.len() == t,
                forall|k: int| 0 <= k < positions.len() ==> positions[k] == 0,
            decreases n + 1 - t,
        {
            let ghost old_positions = positions@;
            positions.push(0i64);
            t += 1;
            proof {
                assert(positions@ == old_positions.push(0i64));
                assert forall|k: int| 0 <= k < positions.len() implies positions[k] == 0 by {
                    if k < old_positions.len() {
                    } else {
                        assert(k == old_positions.len());
                    }
                }
            }
        }
        let mut i = 0usize;
        while i < n
            invariant
                n == permutation.len(),
                is_valid_permutation(permutation@),
                all_values_occur(permutation@),
                are_valid_queries(queries@, permutation.len() as int),
                positions.len() == n + 1,
                0 <= i <= n,
                forall|k: int| 0 <= k < i as int ==> #[trigger] positions[permutation[k] as int] == k + 1,
                forall|k: int| 0 <= k < positions.len() ==> 0 <= #[trigger] positions[k] <= n as int,
            decreases n - i,
        {
            let value = permutation[i] as usize;
            let ghost old_positions = positions@;
            positions.set(value, i as i64 + 1);
            proof {
                assert(1 <= permutation[i as int] <= n as int);
                assert(value == permutation[i as int] as usize);
                assert(positions@ == old_positions.update(value as int, (i + 1) as i64));
                assert(0 <= i as int + 1 <= n as int);
                assert forall|k: int| 0 <= k < i as int + 1 implies #[trigger] positions[permutation[k] as int] == k + 1 by {
                    if k == i as int {
                        assert(permutation[k] == permutation[i as int]);
                        assert(positions[permutation[k] as int] == i as int + 1);
                    } else {
                        assert(0 <= k < i as int);
                        assert(old_positions[permutation[k] as int] == k + 1);
                        if permutation[k] as int == value as int {
                            assert(k < i as int);
                            assert(permutation[k] != permutation[i as int]);
                        } else {
                            assert(positions[permutation[k] as int] == old_positions[permutation[k] as int]);
                        }
                    }
                }
                assert forall|k: int| 0 <= k < positions.len() implies 0 <= #[trigger] positions[k] <= n as int by {
                    if k == value as int {
                        assert(positions[k] == i as int + 1);
                    } else {
                        assert(positions[k] == old_positions[k]);
                    }
                }
            }
            i += 1;
        }
        proof {
            assert(i == n);
            assert forall|value: int| 1 <= value <= n as int implies #[trigger] positions[value] == position_of(permutation@, value) + 1 by {
                lemma_position_of_properties(permutation@, value);
                let pos = position_of(permutation@, value);
                assert(0 <= pos < i as int);
                assert(permutation[pos] == value);
                assert(positions[permutation[pos] as int] == pos + 1);
            }
        }
        let mut vasya = 0i64;
        let mut petya = 0i64;
        let mut j = 0usize;
        while j < queries.len()
            invariant
                n == permutation.len(),
                is_valid_permutation(permutation@),
                all_values_occur(permutation@),
                are_valid_queries(queries@, permutation.len() as int),
                positions.len() == n + 1,
                forall|value: int| 1 <= value <= n as int ==> #[trigger] positions[value] == position_of(permutation@, value) + 1,
                0 <= j <= queries.len(),
                vasya as int == total_vasya(permutation@, queries@, j as int),
                petya as int == total_petya(permutation@, queries@, j as int),
                0 <= vasya as int <= j as int * 100_000,
                0 <= petya as int <= j as int * 100_000,
            decreases queries.len() - j,
        {
            let value = queries[j] as usize;
            let p = positions[value];
            proof {
                lemma_total_vasya_step(permutation@, queries@, j as int);
                lemma_total_petya_step(permutation@, queries@, j as int);
                lemma_position_of_properties(permutation@, queries[j as int] as int);
                lemma_total_bounds(permutation@, queries@, j as int + 1);
                assert(1 <= queries[j as int] <= n as int);
                assert(value == queries[j as int] as usize);
                assert(p as int == position_of(permutation@, queries[j as int] as int) + 1);
                assert(n as int - p as int + 1 == permutation.len() - position_of(permutation@, queries[j as int] as int));
                assert(0 <= p <= n as int);
                assert(vasya as int + p as int == total_vasya(permutation@, queries@, j as int + 1));
                assert(petya as int + (n as int - p as int + 1) == total_petya(permutation@, queries@, j as int + 1));
                assert((j as int + 1) * 100_000 <= 100_000 * 100_000);
            }
            vasya += p;
            petya += n as i64 - p + 1;
            j += 1;
        }
        (vasya, petya)
    }
}

}
