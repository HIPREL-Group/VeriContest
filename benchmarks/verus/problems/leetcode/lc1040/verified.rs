use vstd::prelude::*;
use vstd::seq_lib::*;

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

proof fn lemma_multiset_swap(seq: Seq<i32>, i: int, j: int)
    requires
        0 <= i < seq.len(),
        0 <= j < seq.len(),
        i != j,
    ensures
        seq.update(i, seq[j]).update(j, seq[i]).to_multiset() =~= seq.to_multiset(),
{
    broadcast use group_to_multiset_ensures;
    let after_first = seq.update(i, seq[j]);
    assert(after_first.to_multiset() =~= seq.to_multiset().insert(seq[j]).remove(seq[i]));
    assert(after_first[j] == seq[j]);
    assert(after_first.update(j, seq[i]).to_multiset()
        =~= after_first.to_multiset().insert(seq[i]).remove(after_first[j]));
}

proof fn left_bound_skip(s: Seq<i32>, j: int, skip: int, start: int)
    requires
        0 <= start <= skip <= j < s.len(),
        s.len() >= 3,
        forall |k: int| start <= k < skip ==>
            (s[j] as int) - (s[k] as int) >= (s.len() as int),
    ensures
        left_bound(s, j, start) == left_bound(s, j, skip),
    decreases skip - start
{
    if start < skip {
        left_bound_skip(s, j, skip, start + 1);
    }
}

proof fn left_bound_in_range(s: Seq<i32>, j: int, start: int)
    requires
        is_sorted(s),
        0 <= start <= j < s.len(),
        s.len() >= 1,
    ensures
        start <= left_bound(s, j, start) <= j,
    decreases j - start + 1
{
    if !((s[j] as int) - (s[start] as int) < (s.len() as int)) {
        if start < j {
            left_bound_in_range(s, j, start + 1);
        }
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
        let ghost original = stones@;
        let mut stones = stones;
        let n = stones.len();

        
        let mut si: usize = 1;
        while si < n
            invariant
                1 <= si <= n,
                n == stones.len(),
                n >= 3,
                n <= 10000,
                stones@.to_multiset() =~= original.to_multiset(),
                forall |a: int, b: int| 0 <= a < b < si as int ==>
                    stones@[a] < stones@[b],
                forall |a: int, b: int| 0 <= a < b < n as int ==>
                    stones@[a] != stones@[b],
                forall |k: int| 0 <= k < n as int ==>
                    1 <= #[trigger] stones@[k] <= 1_000_000_000i32,
            decreases n - si
        {
            let mut sj: usize = si;
            while sj > 0 && stones[sj - 1] > stones[sj]
                invariant
                    0 <= sj <= si,
                    si < n,
                    n == stones.len(),
                    n >= 3,
                    n <= 10000,
                    stones@.to_multiset() =~= original.to_multiset(),
                    forall |a: int, b: int| 0 <= a < b < sj as int ==>
                        stones@[a] < stones@[b],
                    forall |a: int, b: int| sj as int <= a && a < b && b <= si as int ==>
                        stones@[a] < stones@[b],
                    forall |a: int, b: int|
                        (0 <= a && a < (sj as int) && (sj as int) < b && b <= (si as int)) ==>
                        stones@[a] < stones@[b],
                    forall |a: int, b: int| 0 <= a < b < n as int ==>
                        stones@[a] != stones@[b],
                    forall |k: int| 0 <= k < n as int ==>
                        1 <= #[trigger] stones@[k] <= 1_000_000_000i32,
                decreases sj
            {
                proof {
                    lemma_multiset_swap(stones@, sj as int, sj as int - 1);
                }
                let tmp = stones[sj];
                stones.set(sj, stones[sj - 1]);
                stones.set(sj - 1, tmp);
                sj = sj - 1;
            }

            proof {
                if sj > 0 {
                    assert(stones@[(sj - 1) as int] != stones@[sj as int]);
                    assert forall |a: int, b: int|
                        0 <= a && a < b && b <= si as int
                    implies stones@[a] < stones@[b] by {
                        if b < sj as int {
                        } else if a >= sj as int {
                        } else if b > sj as int {
                        } else {
                            assert(b == sj as int);
                            if a < sj as int - 1 {
                                assert(stones@[a] < stones@[(sj - 1) as int]);
                            }
                        }
                    };
                }
            }

            si = si + 1;
        }

        proof {
            assert(is_sorted(stones@));
            assert(same_multiset(stones@, original));
        }

        let ghost s = stones@;

        let max_left = stones[n - 1] - stones[1] - n as i32 + 2;
        let max_right = stones[n - 2] - stones[0] - n as i32 + 2;
        let max_moves = if max_left >= max_right { max_left } else { max_right };

        let mut min_moves: i32 = n as i32;
        let mut i: usize = 0;
        let mut j: usize = 0;

        while j < n
            invariant
                0 <= j <= n,
                0 <= i <= j,
                n == stones@.len(),
                n >= 3,
                n <= 10000,
                s =~= stones@,
                is_sorted(s),
                forall |k: int| 0 <= k < stones@.len() ==>
                    1 <= #[trigger] stones[k] <= 1_000_000_000i32,
                min_moves as int == min_cost(s, j as int - 1),
                0 <= min_moves <= n as i32,
                j < n ==> forall |k: int|
                    0 <= k < i as int ==>
                    (s[j as int] as int) - (s[k] as int) >= (n as int),
            decreases n - j
        {
            while stones[j] - stones[i] >= n as i32
                invariant
                    0 <= i <= j,
                    j < n,
                    n == stones@.len(),
                    n >= 3,
                    n <= 10000,
                    s =~= stones@,
                    is_sorted(s),
                    forall |k: int| 0 <= k < stones@.len() ==>
                        1 <= #[trigger] stones[k] <= 1_000_000_000i32,
                    forall |k: int|
                        0 <= k < i as int ==>
                        (s[j as int] as int) - (s[k] as int) >= (n as int),
                decreases j - i
            {
                i = i + 1;
            }

            proof {
                left_bound_skip(s, j as int, i as int, 0);
                assert(left_bound(s, j as int, 0) == i as int);
            }

            let count = (j - i + 1) as i32;

            if count == n as i32 - 1 && stones[j] - stones[i] == n as i32 - 2 {
                if 2 < min_moves {
                    min_moves = 2;
                }
            } else {
                let cost = n as i32 - count;
                if cost < min_moves {
                    min_moves = cost;
                }
            }

            proof {
                assert(min_moves as int == min_of(
                    cost_at(s, j as int), min_cost(s, j as int - 1)));
            }

            j = j + 1;

            proof {
                if j < n {
                    assert forall |k: int| 0 <= k < i as int
                        implies (s[j as int] as int) - (s[k] as int) >= (n as int)
                    by {
                        assert(s[j as int] > s[(j - 1) as int]);
                    }
                }
            }
        }

        let mut result = Vec::new();
        result.push(min_moves);
        result.push(max_moves);
        result
    }
}

}
