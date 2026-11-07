use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_host_guest_match(home: Seq<i32>, away: Seq<i32>, i: int, j: int) -> bool
    recommends 0 <= i < home.len(), 0 <= j < away.len(),
{
    i != j && home[i] == away[j]
}

pub open spec fn count_matches_at_i(home: Seq<i32>, away: Seq<i32>, i: int, j_end: int) -> nat
    recommends
        0 <= i < home.len(),
        0 <= j_end <= away.len(),
    decreases j_end,
{
    if j_end <= 0 {
        0nat
    } else {
        let j = j_end - 1;
        let inc = if is_host_guest_match(home, away, i, j) { 1nat } else { 0nat };
        count_matches_at_i(home, away, i, j_end - 1) + inc
    }
}

pub open spec fn count_host_guest_pairs(home: Seq<i32>, away: Seq<i32>, n: int, total_n: int) -> nat
    recommends
        0 <= n <= total_n,
        0 <= total_n <= home.len(),
        0 <= total_n <= away.len(),
    decreases n,
{
    if n <= 0 {
        0nat
    } else {
        let i = n - 1;
        count_host_guest_pairs(home, away, n - 1, total_n)
            + count_matches_at_i(home, away, i, total_n)
    }
}

proof fn lemma_count_matches_at_i_step(
    home: Seq<i32>,
    away: Seq<i32>,
    i: int,
    j: int,
    n: int,
)
    requires
        0 <= i < home.len(),
        0 <= j < n,
        n <= away.len(),
    ensures
        count_matches_at_i(home, away, i, j + 1)
            == count_matches_at_i(home, away, i, j)
            + (if is_host_guest_match(home, away, i, j) { 1nat } else { 0nat }),
{
    reveal_with_fuel(count_matches_at_i, 2);
    reveal_with_fuel(is_host_guest_match, 1);
}

proof fn lemma_count_matches_at_i_bounded(
    home: Seq<i32>,
    away: Seq<i32>,
    i: int,
    j: int,
)
    requires
        0 <= i < home.len(),
        0 <= j <= away.len(),
    ensures
        count_matches_at_i(home, away, i, j) <= j as nat,
    decreases j,
{
    if j > 0 {
        lemma_count_matches_at_i_bounded(home, away, i, j - 1);
        reveal_with_fuel(count_matches_at_i, 2);
    } else {
        reveal_with_fuel(count_matches_at_i, 1);
    }
}

proof fn lemma_count_host_guest_step(
    home: Seq<i32>,
    away: Seq<i32>,
    i: int,
    total_n: int,
)
    requires
        0 <= i < total_n,
        total_n <= home.len(),
        total_n <= away.len(),
    ensures
        count_host_guest_pairs(home, away, i + 1, total_n)
            == count_host_guest_pairs(home, away, i, total_n)
            + count_matches_at_i(home, away, i, total_n),
    decreases i,
{
    reveal_with_fuel(count_host_guest_pairs, 2);
    reveal_with_fuel(count_matches_at_i, 1);
}

proof fn lemma_count_host_guest_bounded(
    home: Seq<i32>,
    away: Seq<i32>,
    i: int,
    total_n: int,
)
    requires
        0 <= i <= total_n,
        total_n <= home.len(),
        total_n <= away.len(),
    ensures
        (count_host_guest_pairs(home, away, i, total_n) as int) <= i * total_n,
    decreases i,
{
    if i > 0 {
        lemma_count_host_guest_bounded(home, away, i - 1, total_n);
        lemma_count_matches_at_i_bounded(home, away, i - 1, total_n);
        reveal_with_fuel(count_host_guest_pairs, 2);
        reveal_with_fuel(count_matches_at_i, 1);
        assert((count_matches_at_i(home, away, i - 1, total_n) as int) <= total_n);
        assert((count_host_guest_pairs(home, away, i, total_n) as int)
            == (count_host_guest_pairs(home, away, i - 1, total_n) as int)
                + (count_matches_at_i(home, away, i - 1, total_n) as int));
        assert((count_host_guest_pairs(home, away, i, total_n) as int) <= (i - 1) * total_n + total_n);
        assert((i - 1) * total_n + total_n == i * total_n) by (nonlinear_arith);
    } else {
        reveal_with_fuel(count_host_guest_pairs, 1);
    }
}

impl Solution {
    pub fn count_host_guest_uniforms(home: Vec<i32>, away: Vec<i32>, n: usize) -> (result: usize)
        requires
            2 <= n <= 30,
            home.len() == n,
            away.len() == n,
            forall|i: int| 0 <= i < home.len() as int ==> 1 <= #[trigger] home[i] <= 100,
            forall|i: int| 0 <= i < away.len() as int ==> 1 <= #[trigger] away[i] <= 100,
            forall|i: int| 0 <= i < home.len() as int ==> home[i] as int != away[i] as int,
        ensures
            result as nat == count_host_guest_pairs(home@, away@, n as int, n as int),
    {
        proof {
            assert(900 < 4294967296) by (nonlinear_arith);
            assert(900 < 18446744073709551616) by (nonlinear_arith);
        }
        let mut count = 0usize;
        let mut i = 0usize;
        while i < n
            invariant
                2 <= n <= 30,
                home.len() == n,
                away.len() == n,
                forall|k: int| 0 <= k < home.len() as int ==> 1 <= #[trigger] home[k] <= 100,
                forall|k: int| 0 <= k < away.len() as int ==> 1 <= #[trigger] away[k] <= 100,
                0 <= i <= n,
                count as nat == count_host_guest_pairs(home@, away@, i as int, n as int),
                (count as int) <= 900,
                900 < 4294967296,
            decreases n - i,
        {
            proof {
                lemma_count_host_guest_bounded(home@, away@, i as int, n as int);
                assert((count_host_guest_pairs(home@, away@, i as int, n as int) as int) <= (i as int) * (n as int));
                assert((i as int) <= 30);
                assert((n as int) <= 30);
                assert((i as int) * (n as int) <= 900) by (nonlinear_arith) requires (i as int) < (n as int), (n as int) <= 30;
                assert((count as int) <= 900);
            }
            let mut j = 0usize;
            while j < n
                invariant
                    2 <= n <= 30,
                    home.len() == n,
                    away.len() == n,
                    i < n,
                    count as nat == count_host_guest_pairs(home@, away@, i as int, n as int)
                        + count_matches_at_i(home@, away@, i as int, j as int),
                    0 <= j <= n,
                    (count as int) <= 900,
                    900 < 4294967296,
                decreases n - j,
            {
                if i != j && home[i] == away[j] {
                    proof {
                        lemma_count_matches_at_i_step(
                            home@,
                            away@,
                            i as int,
                            j as int,
                            n as int,
                        );
                        assert(is_host_guest_match(home@, away@, i as int, j as int));
                        assert(count_matches_at_i(home@, away@, i as int, (j as int) + 1)
                            == count_matches_at_i(home@, away@, i as int, j as int) + 1nat);
                        lemma_count_host_guest_bounded(home@, away@, i as int, n as int);
                        lemma_count_matches_at_i_bounded(home@, away@, i as int, j as int);
                        assert((count_host_guest_pairs(home@, away@, i as int, n as int) as int) <= (i as int) * (n as int));
                        assert((count_matches_at_i(home@, away@, i as int, j as int) as int) <= j as int);
                        assert((count as int) == (count_host_guest_pairs(home@, away@, i as int, n as int) as int) + (count_matches_at_i(home@, away@, i as int, j as int) as int));
                        assert((count as int) <= (i as int) * (n as int) + (j as int));
                        assert((n as int) <= 30);
                        assert((i as int) * (n as int) + (j as int) + 1 <= 900) by (nonlinear_arith) requires (i as int) < (n as int), (n as int) <= 30, (j as int) < (n as int);
                        assert((count as int) + 1 <= 900);
                    }
                    count += 1;
                }
                proof {
                    lemma_count_matches_at_i_step(
                        home@,
                        away@,
                        i as int,
                        j as int,
                        n as int,
                    );
                    assert(count as nat == count_host_guest_pairs(home@, away@, i as int, n as int)
                        + count_matches_at_i(home@, away@, i as int, (j as int) + 1));
                }
                j += 1;
            }
            proof {
                lemma_count_host_guest_step(home@, away@, i as int, n as int);
                assert(count as nat == count_host_guest_pairs(home@, away@, i as int + 1, n as int));
            }
            i += 1;
        }
        proof {
            assert forall|i: int, j: int|
                0 <= i < (n as int) && 0 <= j < (n as int) implies
                ((i != j && home@[i] == away@[j]) <==> is_host_guest_match(home@, away@, i, j))
            by {
                reveal_with_fuel(is_host_guest_match, 1);
            };
        }
        count
    }
}

}
