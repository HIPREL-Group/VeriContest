use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;





















pub open spec fn has_winning_move(values: Seq<bool>, pos: int, bound: int) -> bool
    decreases bound,
{
    if bound <= 0 {
        false
    } else if bound * bound <= pos && 0 <= pos - bound * bound < values.len()
        && !values[(pos - bound * bound) as int] {
        true
    } else {
        has_winning_move(values, pos, bound - 1)
    }
}




pub open spec fn game_values(n: nat) -> Seq<bool>
    decreases n,
{
    if n == 0 {
        seq![false]
    } else {
        let prev = game_values((n - 1) as nat);
        prev.push(has_winning_move(prev, n as int, n as int))
    }
}



pub open spec fn wins(n: nat) -> bool {
    game_values(n)[n as int]
}

proof fn lemma_game_values_len(n: nat)
    ensures
        game_values(n).len() == n + 1,
    decreases n,
{
    if n > 0 {
        lemma_game_values_len((n - 1) as nat);
    }
}

proof fn lemma_game_values_stable(n: nat, j: int)
    requires
        0 <= j <= n as int,
    ensures
        game_values(n).len() == n + 1,
        game_values(n)[j] == wins(j as nat),
    decreases n as int - j,
{
    lemma_game_values_len(n);
    lemma_game_values_len(j as nat);
    if j == n as int {
    } else {
        lemma_game_values_len((n - 1) as nat);
        lemma_game_values_stable((n - 1) as nat, j);
    }
}

proof fn lemma_has_winning_move_mono(table: Seq<bool>, pos: int, lo: int, hi: int)
    requires
        has_winning_move(table, pos, lo),
        hi >= lo,
    ensures
        has_winning_move(table, pos, hi),
    decreases hi - lo,
{
    if lo == hi {
    } else {
        lemma_has_winning_move_mono(table, pos, lo, hi - 1);
    }
}

proof fn lemma_has_winning_move_extend(table: Seq<bool>, pos: int, from: int, to: int)
    requires
        from >= 0,
        to >= from,
        (from + 1) * (from + 1) > pos,
    ensures
        has_winning_move(table, pos, to) == has_winning_move(table, pos, from),
    decreases to - from,
{
    if to == from {
    } else {
        lemma_has_winning_move_extend(table, pos, from, to - 1);
        assert(to * to >= (from + 1) * (from + 1)) by (nonlinear_arith)
            requires to >= from + 1, from >= 0;
    }
}

proof fn lemma_has_winning_move_equiv_tables(
    t1: Seq<bool>, t2: Seq<bool>, pos: int, bound: int,
)
    requires
        bound >= 0,
        pos >= 0,
        t1.len() >= pos,
        t2.len() >= pos,
        forall|j: int| 0 <= j < pos ==> (#[trigger] t1[j]) == t2[j],
    ensures
        has_winning_move(t1, pos, bound) == has_winning_move(t2, pos, bound),
    decreases bound,
{
    if bound <= 0 {
    } else {
        if bound * bound <= pos && 0 <= pos - bound * bound {
            assert(pos - bound * bound < pos) by (nonlinear_arith)
                requires bound >= 1, bound * bound <= pos;
            if pos - bound * bound < t1.len() {
                assert(t1[(pos - bound * bound) as int] == t2[(pos - bound * bound) as int]);
            }
        }
        lemma_has_winning_move_equiv_tables(t1, t2, pos, bound - 1);
    }
}

impl Solution {
    pub fn winner_square_game(n: i32) -> (res: bool)
        requires
            1 <= n <= 100000,
        ensures
            res == wins(n as nat),
    {
        let n = n as usize;
        let mut dp: Vec<bool> = Vec::new();
        let mut i: usize = 0;
        while i <= n
            invariant
                0 <= i <= n + 1,
                n <= 100000,
                dp@.len() == i,
                forall|j: int| 0 <= j < i as int ==> (#[trigger] dp@[j]) == false,
            decreases n + 1 - i,
        {
            dp.push(false);
            i = i + 1;
        }

        proof {
            assert(dp@[0] == false);
            assert(game_values(0nat) =~= seq![false]);
            assert(wins(0nat) == false);
        }

        i = 1;
        while i <= n
            invariant
                1 <= i <= n + 1,
                n <= 100000,
                dp@.len() == n + 1,
                forall|j: int| 0 <= j < i as int ==> (#[trigger] dp@[j]) == wins(j as nat),
                forall|j: int| i as int <= j <= n as int ==> (#[trigger] dp@[j]) == false,
            decreases n + 1 - i,
        {
            let mut k: usize = 1;
            let mut k_sq: usize = 1;
            let mut found: bool = false;

            while k_sq <= i && !found
                invariant
                    k >= 1,
                    k <= i + 1,
                    k_sq == (k as int) * (k as int),
                    1 <= i <= n,
                    n <= 100000,
                    dp@.len() == n + 1,
                    forall|j: int| 0 <= j < i as int ==> (#[trigger] dp@[j]) == wins(j as nat),
                    !found ==> has_winning_move(dp@, i as int, (k - 1) as int) == false,
                    found ==> has_winning_move(dp@, i as int, i as int),
                decreases i + 1 - k,
            {
                proof {
                    assert(k_sq >= 1) by (nonlinear_arith)
                        requires k >= 1, k_sq == (k as int) * (k as int);
                    assert(i - k_sq < i);
                }
                if !dp[i - k_sq] {
                    proof {
                        assert(k as int <= i as int) by (nonlinear_arith)
                            requires k >= 1, k_sq == (k as int) * (k as int), k_sq <= i as int;
                        lemma_has_winning_move_mono(dp@, i as int, k as int, i as int);
                    }
                    found = true;
                }
                k = k + 1;
                proof {
                    assert(k_sq + 2 * k - 1 == (k as int) * (k as int)) by (nonlinear_arith)
                        requires k_sq == ((k - 1) as int) * ((k - 1) as int), k >= 2;
                    assert((k as int) * (k as int) <= 3 * (i as int) + 1) by (nonlinear_arith)
                        requires k_sq <= i as int, k_sq == ((k - 1) as int) * ((k - 1) as int),
                                 k >= 2, i <= 100000;
                    assert(k <= i + 1) by (nonlinear_arith)
                        requires (k - 1) >= 1, ((k - 1) as int) * ((k - 1) as int) <= i as int;
                }
                k_sq = k_sq + 2 * k - 1;
            }

            proof {
                lemma_game_values_len(i as nat);
                lemma_game_values_len((i - 1) as nat);
                assert(game_values(i as nat) ==
                    game_values((i - 1) as nat).push(
                        has_winning_move(game_values((i - 1) as nat), i as int, i as int)));
                assert(wins(i as nat) == game_values(i as nat)[i as int]);
                assert(wins(i as nat) ==
                    has_winning_move(game_values((i - 1) as nat), i as int, i as int));

                assert forall|j: int| 0 <= j < i as int implies
                    (#[trigger] dp@[j]) == game_values((i - 1) as nat)[j]
                by {
                    lemma_game_values_stable((i - 1) as nat, j);
                };

                lemma_has_winning_move_equiv_tables(
                    dp@, game_values((i - 1) as nat), i as int, i as int);
            }

            if found {
                proof {
                    assert(has_winning_move(dp@, i as int, i as int)
                        == has_winning_move(game_values((i - 1) as nat), i as int, i as int));
                    assert(wins(i as nat) == true);
                }
                dp.set(i, true);
                proof {
                    assert(dp@[i as int] == true);
                    assert(dp@[i as int] == wins(i as nat));
                }
            } else {
                proof {
                    assert(k_sq == (k as int) * (k as int));
                    lemma_has_winning_move_extend(dp@, i as int, (k - 1) as int, i as int);
                    assert(!has_winning_move(dp@, i as int, i as int));
                    assert(has_winning_move(dp@, i as int, i as int)
                        == has_winning_move(game_values((i - 1) as nat), i as int, i as int));
                    assert(wins(i as nat) == false);
                    assert(dp@[i as int] == false);
                    assert(dp@[i as int] == wins(i as nat));
                }
            }

            i = i + 1;
        }
        dp[n]
    }
}

}
