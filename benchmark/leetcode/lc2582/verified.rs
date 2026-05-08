use vstd::arithmetic::div_mod::{
    lemma_mod_bound, lemma_mod_decreases, lemma_mod_equivalence, lemma_mod_is_zero,
    lemma_mod_multiples_basic, lemma_mod_multiples_vanish, lemma_mod_twice,
};
use vstd::arithmetic::logarithm::{lemma_log0, lemma_log_is_ordered, lemma_log_pow, log};
use vstd::arithmetic::mul::{
    lemma_mul_by_zero_is_zero, lemma_mul_increases, lemma_mul_is_distributive_add_other_way,
};
use vstd::arithmetic::power::pow;
use vstd::arithmetic::power2::{lemma2_to64, lemma_pow2, pow2};
use vstd::prelude::*;

fn main() {}

verus! {

pub proof fn lemma_mod_congruent(x: int, y: int, m: int)
    requires
        x % m == y % m,
        0 <= x <= y,
        m > 0,
    ensures
        exists|n: nat| y == #[trigger] (n * m) + x,
    decreases y,
{
    lemma_mod_equivalence(y, x, m);
    let diff = y - x;
    if diff == 0 {
        lemma_mul_by_zero_is_zero(m);
    } else {
        lemma_mod_is_zero(diff as nat, m as nat);
        if diff == m {
            assert(y == 1 * m + x);
        } else {
            lemma_mod_multiples_vanish(-1, y, m);
            lemma_mod_congruent(x, y - m, m);
            let last_n = choose|n: nat| (y - m) == #[trigger] (n * m) + x;
            lemma_mul_is_distributive_add_other_way(m, last_n as int, 1);
        }
    }
}

pub struct Solution;

impl Solution {
    pub open spec fn pass_the_pillow_spec_inner(n: nat, time: nat, pos: nat, dir: bool) -> nat
        decreases time,
    {
        if time == 0 {
            pos
        } else {
            let dir = if pos == 1 {
                true
            } else if pos == n {
                false
            } else {
                dir
            };
            Self::pass_the_pillow_spec_inner(
                n,
                (time - 1) as nat,
                (pos + if dir {
                    1
                } else {
                    -1
                }) as nat,
                dir,
            )
        }
    }

    pub open spec fn pass_the_pillow_spec(n: nat, time: nat) -> nat {
        Self::pass_the_pillow_spec_inner(n, time, 1, true)
    }

    pub proof fn examples() {
        assert(Self::pass_the_pillow_spec(4, 5) == 2) by (compute);
        assert(Self::pass_the_pillow_spec(3, 2) == 3) by (compute);
    }

    pub proof fn lemma_pillow_travels_straight(n: nat, time: nat, pos: nat, dir: bool, steps: nat)
        requires
            2 <= n,
            1 <= pos <= n,
            1 <= pos + if dir {
                steps as int
            } else {
                -steps
            } <= n,
            steps <= time,
        ensures
            Self::pass_the_pillow_spec_inner(n, time, pos, dir) == Self::pass_the_pillow_spec_inner(
                n,
                (time - steps) as nat,
                (pos + if dir {
                    steps as int
                } else {
                    -steps
                }) as nat,
                dir,
            ),
        decreases steps,
    {
        if steps != 0 {
            Self::lemma_pillow_travels_straight(
                n,
                (time - 1) as nat,
                (pos + if dir {
                    1
                } else {
                    -1
                }) as nat,
                dir,
                (steps - 1) as nat,
            );
        }
    }

    pub open spec fn mod_congruent(x: int, y: int, m: int) -> bool {
        x % m == y % m
    }

    pub proof fn lemma_pillow_periodic_base(n: nat, t1: int, t2: int)
        requires
            2 <= n,
            t2 == t1 + 2 * n - 2,
            0 <= t1 < t2,
        ensures
            Self::pass_the_pillow_spec(n, t1 as nat) == Self::pass_the_pillow_spec(n, t2 as nat),
    {
        let halfway = (n - 1) as nat;
        Self::lemma_pillow_travels_straight(n, t2 as nat, 1, true, halfway);
        Self::lemma_pillow_travels_straight(n, (t2 - halfway) as nat, n, false, halfway);
    }

    pub proof fn lemma_pillow_periodic(n: nat, t1: int, t2: int)
        requires
            2 <= n,
            Self::mod_congruent(t1 as int, t2 as int, 2 * n - 2),
            0 <= t1 <= t2,
        ensures
            Self::pass_the_pillow_spec(n, t1 as nat) == Self::pass_the_pillow_spec(n, t2 as nat),
        decreases t2,
    {
        let m = 2 * n - 2;
        lemma_mod_congruent(t1, t2, m);
        let a = choose|a: int| a >= 0 && t2 == #[trigger] (a * m) + t1;
        if a == 0 {
            
        } else if a == 1 {
            Self::lemma_pillow_periodic_base(n, t1, t2);
        } else {
            lemma_mod_multiples_vanish(-1, t2, m);
            lemma_mul_is_distributive_add_other_way(m, a, -1);
            lemma_mul_increases(a - 1, m);
            Self::lemma_pillow_periodic(n, t1, t2 - m);
            Self::lemma_pillow_periodic_base(n, t2 - m, t2);
        }
    }

    pub fn pass_the_pillow(n: i32, time: i32) -> (res: i32)
        requires
            2 <= n <= 1000,
            1 <= time <= 1000,
        ensures
            res == Self::pass_the_pillow_spec(n as nat, time as nat) as i32,
    {
        let m = 2 * n - 2;
        let t = time % m;
        proof {
            lemma_mod_twice(time as int, m as int);
            lemma_mod_bound(time as int, m as int);
            lemma_mod_decreases(time as nat, m as nat);
            Self::lemma_pillow_periodic(n as nat, t as int, time as int);
        }
        if t < n {
            proof {
                Self::lemma_pillow_travels_straight(n as nat, t as nat, 1, true, t as nat);
            }
            t + 1
        } else {
            proof {
                Self::lemma_pillow_travels_straight(n as nat, t as nat, 1, true, (n - 1) as nat);
                Self::lemma_pillow_travels_straight(
                    n as nat,
                    (t - (n - 1)) as nat,
                    n as nat,
                    false,
                    (t - (n - 1)) as nat,
                );
            }
            2 * n - t - 1
        }
    }
}

} 
