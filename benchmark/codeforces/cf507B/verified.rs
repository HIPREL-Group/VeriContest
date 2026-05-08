use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn square(x: int) -> int {
    x * x
}

pub open spec fn distance_sq(x: int, y: int, x2: int, y2: int) -> int {
    square(x2 - x) + square(y2 - y)
}

pub open spec fn jump_sq(r: int) -> int {
    square(2 * r)
}

pub open spec fn can_reach_in_steps(r: int, x: int, y: int, x2: int, y2: int, steps: int) -> bool {
    0 <= steps && distance_sq(x, y, x2, y2) <= jump_sq(r) * steps * steps
}

proof fn lemma_max_steps_suffice(r: int, x: int, y: int, x2: int, y2: int)
    requires
        1 <= r <= 100000,
        -100000 <= x <= 100000,
        -100000 <= y <= 100000,
        -100000 <= x2 <= 100000,
        -100000 <= y2 <= 100000,
    ensures
        can_reach_in_steps(r, x, y, x2, y2, 200000),
{
    assert(-200000 <= x2 - x) by (nonlinear_arith)
        requires
            x <= 100000,
            -100000 <= x2,
    {
    }
    assert(x2 - x <= 200000) by (nonlinear_arith)
        requires
            -100000 <= x,
            x2 <= 100000,
    {
    }
    assert(-200000 <= y2 - y) by (nonlinear_arith)
        requires
            y <= 100000,
            -100000 <= y2,
    {
    }
    assert(y2 - y <= 200000) by (nonlinear_arith)
        requires
            -100000 <= y,
            y2 <= 100000,
    {
    }
    assert((x2 - x) * (x2 - x) <= 40000000000) by (nonlinear_arith)
        requires
            -200000 <= x2 - x,
            x2 - x <= 200000,
    {
    }
    assert((y2 - y) * (y2 - y) <= 40000000000) by (nonlinear_arith)
        requires
            -200000 <= y2 - y,
            y2 - y <= 200000,
    {
    }
    assert(distance_sq(x, y, x2, y2) <= 80000000000) by (nonlinear_arith)
        requires
            (x2 - x) * (x2 - x) <= 40000000000,
            (y2 - y) * (y2 - y) <= 40000000000,
    {
    }
    assert(80000000000 <= jump_sq(r) * 200000 * 200000) by (nonlinear_arith)
        requires
            1 <= r,
    {
    }
}

impl Solution {
    pub fn min_steps_to_target(r: i128, x: i128, y: i128, x2: i128, y2: i128) -> (res: i128)
        requires
            1 <= r <= 100000,
            -100000 <= x <= 100000,
            -100000 <= y <= 100000,
            -100000 <= x2 <= 100000,
            -100000 <= y2 <= 100000,
        ensures
            0 <= res <= 200000,
            can_reach_in_steps(r as int, x as int, y as int, x2 as int, y2 as int, res as int),
            forall|k: int|
                0 <= k < res as int ==> !can_reach_in_steps(r as int, x as int, y as int, x2 as int, y2 as int, k),
    {
        proof {
            assert(-200000 <= x2 - x) by (nonlinear_arith)
                requires
                    x <= 100000,
                    -100000 <= x2,
            {
            }
            assert(x2 - x <= 200000) by (nonlinear_arith)
                requires
                    -100000 <= x,
                    x2 <= 100000,
            {
            }
            assert(-200000 <= y2 - y) by (nonlinear_arith)
                requires
                    y <= 100000,
                    -100000 <= y2,
            {
            }
            assert(y2 - y <= 200000) by (nonlinear_arith)
                requires
                    -100000 <= y,
                    y2 <= 100000,
            {
            }
            assert(0 <= (x2 - x) * (x2 - x) <= 40000000000) by (nonlinear_arith)
                requires
                    -200000 <= x2 - x,
                    x2 - x <= 200000,
            {
            }
            assert(0 <= (y2 - y) * (y2 - y) <= 40000000000) by (nonlinear_arith)
                requires
                    -200000 <= y2 - y,
                    y2 - y <= 200000,
            {
            }
            assert(0 <= 2 * r <= 200000) by (nonlinear_arith)
                requires
                    1 <= r <= 100000,
            {
            }
        }
        let dx = x2 - x;
        let dy = y2 - y;
        let dist_sq = dx * dx + dy * dy;
        let two_r = 2 * r;
        proof {
            assert(0 <= two_r <= 200000) by (nonlinear_arith)
                requires
                    two_r == 2 * r,
                    1 <= r <= 100000,
            {
            }
            assert(0 <= two_r * two_r < 170141183460469231731687303715884105728) by (nonlinear_arith)
                requires
                    0 <= two_r <= 200000,
            {
            }
        }
        let jump_sq_val = two_r * two_r;
        proof {
            assert(0 <= dist_sq <= 80000000000) by (nonlinear_arith)
                requires
                    dist_sq == dx * dx + dy * dy,
                    0 <= (x2 - x) * (x2 - x) <= 40000000000,
                    0 <= (y2 - y) * (y2 - y) <= 40000000000,
                    dx == x2 - x,
                    dy == y2 - y,
            {
            }
            assert(0 <= jump_sq_val <= 40000000000) by (nonlinear_arith)
                requires
                    jump_sq_val == two_r * two_r,
                    0 <= two_r <= 200000,
            {
            }
            assert(dist_sq as int == distance_sq(x as int, y as int, x2 as int, y2 as int)) by (nonlinear_arith)
                requires
                    dist_sq == dx * dx + dy * dy,
                    dx == x2 - x,
                    dy == y2 - y,
            {
            }
            assert(jump_sq_val as int == jump_sq(r as int)) by (nonlinear_arith)
                requires
                    jump_sq_val == two_r * two_r,
                    two_r == 2 * r,
            {
            }
        }
        let mut ans = 0i128;
        while ans < 200000 && jump_sq_val * ans * ans < dist_sq
            invariant
                1 <= r <= 100000,
                -100000 <= x <= 100000,
                -100000 <= y <= 100000,
                -100000 <= x2 <= 100000,
                -100000 <= y2 <= 100000,
                0 <= dist_sq <= 80000000000,
                0 <= jump_sq_val <= 40000000000,
                dist_sq as int == distance_sq(x as int, y as int, x2 as int, y2 as int),
                jump_sq_val as int == jump_sq(r as int),
                0 <= ans <= 200000,
                0 <= jump_sq_val * ans <= 8000000000000000,
                0 <= jump_sq_val * ans * ans <= 1600000000000000000000,
                forall|k: int|
                    0 <= k < ans as int ==> !can_reach_in_steps(r as int, x as int, y as int, x2 as int, y2 as int, k),
            decreases 200000 - ans,
        {
            let ghost prev_ans = ans;
            proof {
                assert(!can_reach_in_steps(r as int, x as int, y as int, x2 as int, y2 as int, prev_ans as int)) by {
                    assert(0 <= prev_ans as int);
                    assert(jump_sq(r as int) * (prev_ans as int) * (prev_ans as int)
                        == jump_sq_val as int * (prev_ans as int) * (prev_ans as int)) by (nonlinear_arith)
                        requires
                            jump_sq_val as int == jump_sq(r as int),
                    {
                    }
                    assert(jump_sq_val as int * (prev_ans as int) * (prev_ans as int) < dist_sq as int) by (nonlinear_arith)
                        requires
                            jump_sq_val * prev_ans * prev_ans < dist_sq,
                    {
                    }
                }
            }
            ans += 1;
            proof {
                assert(0 <= jump_sq_val * ans <= 8000000000000000) by (nonlinear_arith)
                    requires
                        0 <= jump_sq_val <= 40000000000,
                        0 <= ans <= 200000,
                {
                }
                assert(0 <= jump_sq_val * ans * ans <= 1600000000000000000000) by (nonlinear_arith)
                    requires
                        0 <= jump_sq_val <= 40000000000,
                        0 <= ans <= 200000,
                {
                }
                assert forall|k: int|
                    0 <= k < ans as int implies !can_reach_in_steps(r as int, x as int, y as int, x2 as int, y2 as int, k) by {
                    if k < prev_ans as int {
                    } else {
                        assert(k == prev_ans as int);
                    }
                }
            }
        }
        proof {
            if ans == 200000 {
                lemma_max_steps_suffice(r as int, x as int, y as int, x2 as int, y2 as int);
            } else {
                assert(ans < 200000);
                assert(dist_sq as int <= jump_sq_val as int * (ans as int) * (ans as int)) by (nonlinear_arith)
                    requires
                        !(jump_sq_val * ans * ans < dist_sq),
                {
                }
                assert(can_reach_in_steps(r as int, x as int, y as int, x2 as int, y2 as int, ans as int));
            }
            assert forall|k: int|
                0 <= k < ans as int implies !can_reach_in_steps(r as int, x as int, y as int, x2 as int, y2 as int, k) by {
            }
        }
        ans
    }
}

}
