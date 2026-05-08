use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn abs_diff_digits(a: int, b: int) -> int {
    if a <= b {
        b - a
    } else {
        a - b
    }
}

pub open spec fn digit_circular_moves(a: int, b: int) -> int {
    let d = abs_diff_digits(a, b);
    if d <= 5 {
        d
    } else {
        10 - d
    }
}

pub open spec fn sum_lock_moves(init: Seq<u8>, goal: Seq<u8>, end: int) -> int
    recommends
        init.len() == goal.len(),
        0 <= end <= init.len(),
    decreases end,
{
    if end <= 0 {
        0
    } else {
        let prev = end - 1;
        sum_lock_moves(init, goal, prev)
            + digit_circular_moves(init[prev] as int, goal[prev] as int)
    }
}

proof fn lemma_digit_move_bounded(a: int, b: int)
    requires
        0 <= a <= 9,
        0 <= b <= 9,
    ensures
        0 <= digit_circular_moves(a, b) <= 5,
{
    let ad = abs_diff_digits(a, b);
    assert(0 <= ad <= 9);
    if ad <= 5 {
        assert(digit_circular_moves(a, b) == ad);
        assert(ad <= 5);
    } else {
        assert(6 <= ad <= 9);
        assert(digit_circular_moves(a, b) == 10 - ad);
        assert(10 - ad <= 4);
    }
}

proof fn lemma_u32_diff_matches_abs(ca: u8, cb: u8)
    requires
        ca <= 9,
        cb <= 9,
    ensures
        ({
            let ca32 = ca as u32;
            let cb32 = cb as u32;
            let d = if ca32 >= cb32 {
                ca32 - cb32
            } else {
                cb32 - ca32
            };
            d as int == abs_diff_digits(ca as int, cb as int)
        }),
{
    let ca32 = ca as u32;
    let cb32 = cb as u32;
    let d = if ca32 >= cb32 {
        ca32 - cb32
    } else {
        cb32 - ca32
    };
    if (ca as int) <= (cb as int) {
        assert(ca32 <= cb32);
        assert(d == cb32 - ca32);
        assert(d as int == (cb as int) - (ca as int));
        assert(abs_diff_digits(ca as int, cb as int) == (cb as int) - (ca as int));
    } else {
        assert((cb as int) < (ca as int));
        assert(cb32 < ca32);
        assert(d == ca32 - cb32);
        assert(d as int == (ca as int) - (cb as int));
        assert(abs_diff_digits(ca as int, cb as int) == (ca as int) - (cb as int));
    }
}

proof fn lemma_u32_add_matches_spec(ca: u8, cb: u8)
    requires
        ca <= 9,
        cb <= 9,
    ensures
        ({
            let ca32 = ca as u32;
            let cb32 = cb as u32;
            let d = if ca32 >= cb32 {
                ca32 - cb32
            } else {
                cb32 - ca32
            };
            let add = if d <= 5 {
                d
            } else {
                10 - d
            };
            add as int == digit_circular_moves(ca as int, cb as int)
        }),
{
    lemma_u32_diff_matches_abs(ca, cb);
    let ca32 = ca as u32;
    let cb32 = cb as u32;
    let d = if ca32 >= cb32 {
        ca32 - cb32
    } else {
        cb32 - ca32
    };
    assert(d as int == abs_diff_digits(ca as int, cb as int));
    assert(0 <= d <= 9);
    let add = if d <= 5 {
        d
    } else {
        10 - d
    };
    let di = abs_diff_digits(ca as int, cb as int);
    assert(d as int == di);
    if di <= 5 {
        assert(d <= 5);
        assert(add == d);
        assert(digit_circular_moves(ca as int, cb as int) == di);
        assert(add as int == digit_circular_moves(ca as int, cb as int));
    } else {
        assert(6 <= di <= 9);
        assert(6 <= d <= 9);
        assert(d > 5);
        assert(add == 10 - d);
        assert(digit_circular_moves(ca as int, cb as int) == 10 - di);
        assert((10 - d) as int == 10 - di);
        assert(add as int == digit_circular_moves(ca as int, cb as int));
    }
}

proof fn lemma_sum_lock_moves_step(init: Seq<u8>, goal: Seq<u8>, k: int)
    requires
        init.len() == goal.len(),
        0 <= k < init.len(),
    ensures
        sum_lock_moves(init, goal, k + 1) == sum_lock_moves(init, goal, k)
            + digit_circular_moves(init[k] as int, goal[k] as int),
{
    reveal_with_fuel(sum_lock_moves, 3);
}

proof fn lemma_sum_lock_upper(
    init: Seq<u8>,
    goal: Seq<u8>,
    end: int,
)
    requires
        init.len() == goal.len(),
        0 <= end <= init.len(),
        forall |j: int| 0 <= j < init.len() ==> 0 <= #[trigger] init[j] <= 9,
        forall |j: int| 0 <= j < goal.len() ==> 0 <= #[trigger] goal[j] <= 9,
    ensures
        sum_lock_moves(init, goal, end) <= 5 * end,
    decreases end,
{
    if end <= 0 {
        reveal_with_fuel(sum_lock_moves, 1);
    } else {
        let prev = end - 1;
        assert(0 <= prev < init.len());
        lemma_digit_move_bounded(init[prev] as int, goal[prev] as int);
        lemma_sum_lock_upper(init, goal, prev);
        reveal_with_fuel(sum_lock_moves, 2);
        assert(sum_lock_moves(init, goal, end) == sum_lock_moves(init, goal, prev)
            + digit_circular_moves(init[prev] as int, goal[prev] as int));
        assert(sum_lock_moves(init, goal, prev) <= 5 * prev);
        assert(digit_circular_moves(init[prev] as int, goal[prev] as int) <= 5);
        assert(5 * prev + 5 == 5 * end);
        assert(sum_lock_moves(init, goal, end) <= 5 * end);
    }
}

impl Solution {
    pub fn min_lock_moves(n: usize, current: Vec<u8>, target: Vec<u8>) -> (result: u32)
        requires
            1 <= n <= 1000,
            current.len() == n,
            target.len() == n,
            forall |i: int|
                0 <= i < n as int ==> 0 <= #[trigger] current[i] <= 9,
            forall |i: int|
                0 <= i < n as int ==> 0 <= #[trigger] target[i] <= 9,
        ensures
            result as int == sum_lock_moves(current@, target@, n as int),
    {
        let mut sum: u32 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                1 <= n <= 1000,
                n == current.len(),
                n == target.len(),
                forall |j: int|
                    0 <= j < n as int ==> 0 <= #[trigger] current[j] <= 9,
                forall |j: int|
                    0 <= j < n as int ==> 0 <= #[trigger] target[j] <= 9,
                0 <= i <= n,
                sum as int == sum_lock_moves(current@, target@, i as int),
                sum <= 5000,
            decreases n - i,
        {
            proof {
                lemma_sum_lock_upper(current@, target@, i as int);
                assert(sum_lock_moves(current@, target@, i as int) <= 5 * i as int);
                assert(5 * i as int <= 5000) by (nonlinear_arith)
                    requires i <= n, n <= 1000 {}
            }
            let ci = current[i];
            let ti = target[i];
            proof {
                lemma_u32_add_matches_spec(ci, ti);
            }
            let ca = current[i] as u32;
            let cb = target[i] as u32;
            let d = if ca >= cb {
                ca - cb
            } else {
                cb - ca
            };
            let add = if d <= 5 {
                d
            } else {
                10 - d
            };
            proof {
                lemma_sum_lock_moves_step(current@, target@, i as int);
                assert((sum + add) as int == sum as int + add as int);
                assert(sum as int == sum_lock_moves(current@, target@, i as int));
                let ai = ci as int;
                let bi = ti as int;
                assert(add as int == digit_circular_moves(ai, bi));
                let lhs = sum as int + digit_circular_moves(ai, bi);
                assert(lhs == sum_lock_moves(current@, target@, (i as int) + 1));
            }
            sum = sum + add;
            i = i + 1;
            proof {
                assert(sum as int == sum_lock_moves(current@, target@, i as int));
            }
        }
        proof {
            assert(i == n);
            assert(sum as int == sum_lock_moves(current@, target@, n as int));
            assert(forall |k: int|
                0 <= k < n as int ==> 0 <= digit_circular_moves(
                    #[trigger] current[k] as int,
                    target[k] as int,
                ) <= 5) by {
                assert forall |k: int| 0 <= k < n as int implies {
                    0 <= digit_circular_moves(
                        #[trigger] current[k] as int,
                        target[k] as int,
                    ) <= 5
                } by {
                    assert(0 <= current[k] <= 9);
                    assert(0 <= target[k] <= 9);
                    lemma_digit_move_bounded(current[k] as int, target[k] as int);
                }
            };
        }
        sum
    }
}

}
