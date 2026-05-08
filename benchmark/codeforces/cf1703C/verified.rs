use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn step_digit(x: int, delta: int) -> int {
    ((x + delta) % 10 + 10) % 10
}

pub open spec fn apply_moves_from(x: int, deltas: Seq<i32>, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if lo >= hi {
        x
    } else {
        apply_moves_from(step_digit(x, deltas[lo] as int), deltas, lo + 1, hi)
    }
}

proof fn lemma_apply_unroll(x: int, deltas: Seq<i32>, lo: int, hi: int)
    requires
        lo < hi,
        0 <= lo,
        hi <= deltas.len(),
    ensures
        apply_moves_from(x, deltas, lo, hi) == apply_moves_from(step_digit(x, deltas[lo] as int), deltas, lo + 1, hi),
    decreases hi - lo,
{
}

proof fn lemma_step_undo(x: int, d: int)
    requires
        d == 1 || d == -1,
        0 <= x <= 9,
    ensures
        step_digit(step_digit(x, d), if d == 1 { -1 } else { 1 }) == x,
{
    if d == 1 {
        assert(0 <= x <= 9);
        assert(step_digit(x, 1) == ((x + 1) % 10 + 10) % 10);
        assert((x + 1) % 10 >= 0);
        assert((x + 1) % 10 < 10);
        assert(((x + 1) % 10 + 10) % 10 == (x + 1) % 10);
        let y = step_digit(x, 1);
        assert(0 <= y <= 9);
        assert(step_digit(y, -1) == ((y - 1) % 10 + 10) % 10);
        assert(y == (x + 1) % 10);
        if x < 9 {
            assert(y == x + 1);
            assert(step_digit(y, -1) == ((x + 1 - 1) % 10 + 10) % 10);
            assert(step_digit(y, -1) == x);
        } else {
            assert(x == 9);
            assert(y == 0);
            assert(step_digit(0, -1) == 9);
        }
    } else {
        assert(d == -1);
        assert(0 <= x <= 9);
        let y = step_digit(x, -1);
        assert(0 <= y <= 9);
        assert(step_digit(y, 1) == x);
        if x > 0 {
            assert(y == x - 1);
            assert(step_digit(y, 1) == x);
        } else {
            assert(x == 0);
            assert(y == 9);
            assert(step_digit(9, 1) == 0);
        }
    }
}

proof fn lemma_step_injective(x: int, y: int, d: int)
    requires
        d == 1 || d == -1,
        0 <= x <= 9,
        0 <= y <= 9,
        step_digit(x, d) == step_digit(y, d),
    ensures
        x == y,
{
    let u = if d == 1 { -1 } else { 1 };
    lemma_step_undo(x, d);
    lemma_step_undo(y, d);
    assert(step_digit(step_digit(x, d), u) == x);
    assert(step_digit(step_digit(y, d), u) == y);
    assert(step_digit(step_digit(x, d), u) == step_digit(step_digit(y, d), u));
}

proof fn lemma_apply_injective(deltas: Seq<i32>, lo: int, hi: int, x: int, y: int)
    requires
        0 <= lo <= hi <= deltas.len(),
        forall|j: int| lo <= j < hi ==> #[trigger] deltas[j] == 1 || deltas[j] == -1,
        0 <= x <= 9,
        0 <= y <= 9,
        apply_moves_from(x, deltas, lo, hi) == apply_moves_from(y, deltas, lo, hi),
    ensures
        x == y,
    decreases hi - lo,
{
    if lo >= hi {
        assert(x == y);
    } else {
        lemma_apply_unroll(x, deltas, lo, hi);
        lemma_apply_unroll(y, deltas, lo, hi);
        let sx = step_digit(x, deltas[lo] as int);
        let sy = step_digit(y, deltas[lo] as int);
        assert(apply_moves_from(x, deltas, lo, hi) == apply_moves_from(sx, deltas, lo + 1, hi));
        assert(apply_moves_from(y, deltas, lo, hi) == apply_moves_from(sy, deltas, lo + 1, hi));
        assert(apply_moves_from(sx, deltas, lo + 1, hi) == apply_moves_from(sy, deltas, lo + 1, hi));
        assert(0 <= sx <= 9);
        assert(0 <= sy <= 9);
        lemma_step_digit_in_range(x, deltas[lo] as int);
        lemma_step_digit_in_range(y, deltas[lo] as int);
        lemma_apply_injective(deltas, lo + 1, hi, sx, sy);
        assert(sx == sy);
        lemma_step_injective(x, y, deltas[lo] as int);
    }
}

proof fn lemma_step_digit_in_range(x: int, delta: int)
    requires
        0 <= x <= 9,
        delta == 1 || delta == -1,
    ensures
        0 <= step_digit(x, delta) <= 9,
{
    if delta == 1 {
        assert(step_digit(x, 1) == ((x + 1) % 10 + 10) % 10);
        assert(0 <= (x + 1) % 10 <= 9);
    } else {
        assert(step_digit(x, -1) == ((x - 1) % 10 + 10) % 10);
        assert(0 <= (x - 1 + 10) % 10 <= 9);
    }
}

impl Solution {
    pub fn recover_digit(final_d: i32, move_deltas: Vec<i32>) -> (res: i32)
        requires
            0 <= final_d <= 9,
            move_deltas.len() <= 10,
            forall|j: int|
                0 <= j < move_deltas.len() ==> #[trigger] move_deltas[j] == 1 || move_deltas[j] == -1,
        ensures
            0 <= res <= 9,
            apply_moves_from(res as int, move_deltas@, 0, move_deltas.len() as int) == final_d as int,
            forall|x: int|
                0 <= x <= 9 && #[trigger] apply_moves_from(x, move_deltas@, 0, move_deltas.len() as int) == final_d as int
                    ==> x == res as int,
    {
        let mut x = final_d;
        let mut idx = move_deltas.len();
        while idx > 0
            invariant
                move_deltas.len() <= 10,
                0 <= final_d <= 9,
                forall|j: int|
                    0 <= j < move_deltas.len() as int ==> #[trigger] move_deltas[j] == 1 || move_deltas[j] == -1,
                idx <= move_deltas.len(),
                0 <= x <= 9,
                apply_moves_from(x as int, move_deltas@, idx as int, move_deltas.len() as int) == final_d as int,
            decreases idx,
        {
            proof {
                assert(apply_moves_from(x as int, move_deltas@, idx as int, move_deltas.len() as int) == final_d as int);
                assert(idx > 0);
                assert(idx as int > 0);
            }
            idx = idx - 1;
            let d = move_deltas[idx];
            let old_x = x;
            if d == 1 {
                x = (x - 1 + 10) % 10;
            } else {
                x = (x + 1) % 10;
            }
            proof {
                assert(d == 1 || d == -1);
                assert(0 <= old_x <= 9);
                assert(step_digit(x as int, d as int) == old_x as int) by {
                    if d == 1 {
                        assert(x == (old_x - 1 + 10) % 10);
                        lemma_step_undo(old_x as int, 1);
                        assert(step_digit(old_x as int, 1) == old_x as int + 1 || old_x == 9);
                    } else {
                        lemma_step_undo(old_x as int, -1);
                    }
                };
                lemma_apply_unroll(x as int, move_deltas@, idx as int, move_deltas.len() as int);
                assert(apply_moves_from(x as int, move_deltas@, idx as int, move_deltas.len() as int)
                    == apply_moves_from(step_digit(x as int, d as int), move_deltas@, idx as int + 1, move_deltas.len() as int));
                assert(step_digit(x as int, d as int) == old_x as int);
                assert(apply_moves_from(x as int, move_deltas@, idx as int, move_deltas.len() as int)
                    == apply_moves_from(old_x as int, move_deltas@, idx as int + 1, move_deltas.len() as int));
                assert(apply_moves_from(old_x as int, move_deltas@, idx as int + 1, move_deltas.len() as int) == final_d as int);
            }
        }
        proof {
            assert(apply_moves_from(x as int, move_deltas@, 0, move_deltas.len() as int) == final_d as int);
            assert(forall|z: int|
                0 <= z <= 9 && apply_moves_from(z, move_deltas@, 0, move_deltas.len() as int) == final_d as int
                    ==> z == x as int) by {
                assert forall|z: int|
                    0 <= z <= 9 && apply_moves_from(z, move_deltas@, 0, move_deltas.len() as int) == final_d as int
                        implies z == x as int by {
                    lemma_apply_injective(move_deltas@, 0, move_deltas.len() as int, z, x as int);
                }
            };
        }
        x
    }
}

}
