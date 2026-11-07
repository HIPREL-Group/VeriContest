use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn MOD() -> int {
        1_000_000_007
    }

    pub open spec fn max_pos_spec(steps: int, arr_len: int) -> int {
        if steps / 2 < arr_len - 1 {
            steps / 2
        } else {
            arr_len - 1
        }
    }

    pub open spec fn ways(step: int, pos: int, max_pos: int) -> int
        decreases step,
    {
        if step < 0 || pos < 0 || pos > max_pos {
            0
        } else if step == 0 {
            if pos == 0 { 1 } else { 0 }
        } else {
            Self::ways(step - 1, pos - 1, max_pos)
                + Self::ways(step - 1, pos, max_pos)
                + Self::ways(step - 1, pos + 1, max_pos)
        }
    }

    proof fn ways_nonneg(step: int, pos: int, max_pos: int)
        ensures
            Self::ways(step, pos, max_pos) >= 0,
        decreases step,
    {
        if step < 0 || pos < 0 || pos > max_pos {
        } else if step == 0 {
        } else {
            Self::ways_nonneg(step - 1, pos - 1, max_pos);
            Self::ways_nonneg(step - 1, pos, max_pos);
            Self::ways_nonneg(step - 1, pos + 1, max_pos);
        }
    }

    proof fn lemma_mod_add_three(a: int, b: int, c: int, m: int)
        requires
            m > 0,
            a >= 0,
            b >= 0,
            c >= 0,
        ensures
            (a % m + b % m + c % m) % m == (a + b + c) % m,
    {
        vstd::arithmetic::div_mod::lemma_add_mod_noop(a, b, m);
        vstd::arithmetic::div_mod::lemma_add_mod_noop(a + b, c, m);
        vstd::arithmetic::div_mod::lemma_add_mod_noop(a % m + b % m, c % m, m);
        assert((c % m) % m == c % m) by(nonlinear_arith)
            requires
                m > 0,
                c >= 0,
        ;
        assert(((a + b) % m + c % m) % m == (a % m + b % m + c % m) % m);
    }

    pub fn num_ways(steps: i32, arr_len: i32) -> (result: i32)
        requires
            1 <= steps <= 500,
            1 <= arr_len <= 1_000_000,
        ensures
            result as int == Self::ways(
                steps as int,
                0,
                Self::max_pos_spec(steps as int, arr_len as int),
            ) % Self::MOD(),
    {
        let modulo: i64 = 1_000_000_007;
        let max_p: i32 = if steps / 2 < arr_len - 1 {
            steps / 2
        } else {
            arr_len - 1
        };
        let size: usize = (max_p + 1) as usize;

        let mut cur: Vec<i64> = Vec::new();
        let mut init_i: usize = 0;
        while init_i < size
            invariant
                0 <= init_i <= size,
                cur@.len() == init_i as int,
                forall|k: int| 0 <= k < init_i as int ==> cur@[k] == 0i64,
                size == (max_p + 1) as usize,
            decreases size - init_i,
        {
            cur.push(0i64);
            init_i += 1;
        }
        cur.set(0, 1i64);

        proof {
            assert forall|j: int|
                0 <= j < size as int implies 0 <= (#[trigger] cur@[j]) < modulo
            by {
                if j == 0 {
                    assert(cur@[0] == 1i64);
                } else {
                    assert(cur@[j] == 0i64);
                }
            };
            assert forall|j: int|
                0 <= j < size as int implies (#[trigger] cur@[j]) as int == Self::ways(
                    0,
                    j,
                    max_p as int,
                ) % Self::MOD()
            by {
                if j == 0 {
                    assert(Self::ways(0, 0, max_p as int) == 1);
                } else {
                    assert(Self::ways(0, j, max_p as int) == 0);
                }
            };
        }

        let mut s: i32 = 0;
        while s < steps
            invariant
                0 <= s <= steps,
                1 <= steps <= 500,
                0 <= max_p <= 250,
                max_p as int == Self::max_pos_spec(steps as int, arr_len as int),
                size == (max_p + 1) as usize,
                cur@.len() == size as int,
                modulo == 1_000_000_007i64,
                forall|j: int|
                    0 <= j < size as int ==> 0 <= (#[trigger] cur@[j]) < modulo,
                forall|j: int|
                    0 <= j < size as int ==> (#[trigger] cur@[j]) as int == Self::ways(
                        s as int,
                        j,
                        max_p as int,
                    ) % Self::MOD(),
            decreases steps - s,
        {
            let mut nxt: Vec<i64> = Vec::new();
            let mut init_j: usize = 0;
            while init_j < size
                invariant
                    0 <= init_j <= size,
                    nxt@.len() == init_j as int,
                    forall|k: int| 0 <= k < init_j as int ==> nxt@[k] == 0i64,
                    size == (max_p + 1) as usize,
                decreases size - init_j,
            {
                nxt.push(0i64);
                init_j += 1;
            }

            let mut j: i32 = 0;
            while j <= max_p
                invariant
                    0 <= j <= max_p + 1,
                    0 <= s < steps,
                    0 <= max_p <= 250,
                    max_p as int == Self::max_pos_spec(steps as int, arr_len as int),
                    size == (max_p + 1) as usize,
                    modulo == 1_000_000_007i64,
                    nxt@.len() == size as int,
                    cur@.len() == size as int,
                    forall|k: int|
                        0 <= k < size as int ==> 0 <= (#[trigger] cur@[k]) < modulo,
                    forall|k: int|
                        0 <= k < size as int ==> (#[trigger] cur@[k]) as int == Self::ways(
                            s as int,
                            k,
                            max_p as int,
                        ) % Self::MOD(),
                    forall|k: int|
                        0 <= k < j as int ==> 0 <= (#[trigger] nxt@[k]) < modulo,
                    forall|k: int|
                        0 <= k < j as int ==> (#[trigger] nxt@[k]) as int == Self::ways(
                            (s + 1) as int,
                            k,
                            max_p as int,
                        ) % Self::MOD(),
                    forall|k: int|
                        j as int <= k < size as int ==> nxt@[k] == 0i64,
                decreases max_p + 1 - j,
            {
                let left: i64 = if j > 0 {
                    cur[(j - 1) as usize]
                } else {
                    0i64
                };
                let right: i64 = if j < max_p {
                    cur[(j + 1) as usize]
                } else {
                    0i64
                };
                let stay: i64 = cur[j as usize];

                proof {
                    let a = Self::ways(s as int, (j - 1) as int, max_p as int);
                    let b = Self::ways(s as int, j as int, max_p as int);
                    let c = Self::ways(s as int, (j + 1) as int, max_p as int);
                    let m = Self::MOD();

                    Self::ways_nonneg(s as int, (j - 1) as int, max_p as int);
                    Self::ways_nonneg(s as int, j as int, max_p as int);
                    Self::ways_nonneg(s as int, (j + 1) as int, max_p as int);

                    if j == 0 {
                        assert(a == 0);
                        assert(left as int == 0);
                    }
                    if j == max_p {
                        assert(c == 0);
                        assert(right as int == 0);
                    }

                    assert(stay as int == b % m);
                    assert(left as int == a % m);
                    assert(right as int == c % m);

                    Self::lemma_mod_add_three(a, b, c, m);
                    assert(a + b + c == Self::ways(
                        (s + 1) as int,
                        j as int,
                        max_p as int,
                    ));
                    assert((left + right + stay) as int == a % m + c % m + b % m);
                }

                nxt.set(j as usize, (left + right + stay) % modulo);
                j += 1;
            }

            cur = nxt;
            s += 1;
        }

        proof {
            Self::ways_nonneg(
                steps as int,
                0,
                Self::max_pos_spec(steps as int, arr_len as int),
            );
        }

        cur[0] as i32
    }
}

}
