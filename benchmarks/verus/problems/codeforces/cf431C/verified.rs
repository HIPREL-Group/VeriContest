use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn modulus() -> int {
    1_000_000_007
}

pub open spec fn sum_seq(parts: Seq<int>) -> int
    decreases parts.len(),
{
    if parts.len() == 0 {
        0
    } else {
        sum_seq(parts.drop_last()) + parts[parts.len() - 1]
    }
}

pub open spec fn valid_k_tree_sequence(parts: Seq<int>, total: int, k: int, d: int) -> bool
    recommends
        0 <= total,
        1 <= d <= k,
{
    &&& sum_seq(parts) == total
    &&& forall|i: int| 0 <= i < parts.len() ==> 1 <= #[trigger] parts[i] <= k
    &&& exists|i: int| 0 <= i < parts.len() && parts[i] >= d
}

pub open spec fn step_cap(total: int, k: int) -> int
    recommends
        0 <= total,
        1 <= k,
{
    if total < k { total } else { k }
}

pub open spec fn count_no_large_step(total: int, k: int, d: int, step: int) -> int
    recommends
        0 < total,
        1 <= d <= k,
        0 <= step <= step_cap(total, k),
    decreases total, step when 0 < total && 0 <= step && step <= total && 1 <= d && d <= k
{
    if step == 0 {
        0
    } else {
        count_no_large_step(total, k, d, step - 1)
            + if step < d {
                let rem = total - step;
                if rem == 0 {
                    1
                } else {
                    count_no_large_step(rem, k, d, step_cap(rem, k))
                }
            } else {
                0
            }
    }
}

pub open spec fn count_no_large(total: int, k: int, d: int) -> int
    recommends
        0 <= total,
        1 <= d <= k,
{
    if total == 0 {
        1
    } else {
        count_no_large_step(total, k, d, step_cap(total, k))
    }
}

pub open spec fn count_has_large_step(total: int, k: int, d: int, step: int) -> int
    recommends
        0 < total,
        1 <= d <= k,
        0 <= step <= step_cap(total, k),
    decreases total, step when 0 < total && 0 <= step && step <= total && 1 <= d && d <= k
{
    if step == 0 {
        0
    } else {
        count_has_large_step(total, k, d, step - 1)
            + if step < d {
                let rem = total - step;
                if rem == 0 {
                    0
                } else {
                    count_has_large_step(rem, k, d, step_cap(rem, k))
                }
            } else {
                let rem = total - step;
                if rem == 0 {
                    1
                } else {
                    count_no_large_step(rem, k, d, step_cap(rem, k))
                        + count_has_large_step(rem, k, d, step_cap(rem, k))
                }
            }
    }
}

pub open spec fn count_has_large(total: int, k: int, d: int) -> int
    recommends
        0 <= total,
        1 <= d <= k,
{
    if total == 0 {
        0
    } else {
        count_has_large_step(total, k, d, step_cap(total, k))
    }
}

pub open spec fn count_no_large_step_mod(total: int, k: int, d: int, step: int) -> int
    recommends
        0 < total,
        1 <= d <= k,
        0 <= step <= step_cap(total, k),
    decreases total, step when 0 < total && 0 <= step && step <= total && 1 <= d && d <= k
{
    if step == 0 {
        0
    } else if step < d {
        let rem = total - step;
        if rem == 0 {
            (count_no_large_step_mod(total, k, d, step - 1) + 1) % modulus()
        } else {
            (count_no_large_step_mod(total, k, d, step - 1)
                + count_no_large_step_mod(rem, k, d, step_cap(rem, k))) % modulus()
        }
    } else {
        count_no_large_step_mod(total, k, d, step - 1)
    }
}

pub open spec fn count_no_large_mod(total: int, k: int, d: int) -> int
    recommends
        0 <= total,
        1 <= d <= k,
{
    if total == 0 {
        1
    } else {
        count_no_large_step_mod(total, k, d, step_cap(total, k))
    }
}

pub open spec fn count_has_large_step_mod(total: int, k: int, d: int, step: int) -> int
    recommends
        0 < total,
        1 <= d <= k,
        0 <= step <= step_cap(total, k),
    decreases total, step when 0 < total && 0 <= step && step <= total && 1 <= d && d <= k
{
    if step == 0 {
        0
    } else if step < d {
        let rem = total - step;
        if rem == 0 {
            count_has_large_step_mod(total, k, d, step - 1)
        } else {
            (count_has_large_step_mod(total, k, d, step - 1)
                + count_has_large_step_mod(rem, k, d, step_cap(rem, k))) % modulus()
        }
    } else {
        let rem = total - step;
        if rem == 0 {
            (count_has_large_step_mod(total, k, d, step - 1) + 1) % modulus()
        } else {
            ((count_has_large_step_mod(total, k, d, step - 1)
                + count_no_large_step_mod(rem, k, d, step_cap(rem, k))) % modulus()
                + count_has_large_step_mod(rem, k, d, step_cap(rem, k))) % modulus()
        }
    }
}

pub open spec fn count_has_large_mod(total: int, k: int, d: int) -> int
    recommends
        0 <= total,
        1 <= d <= k,
{
    if total == 0 {
        0
    } else {
        count_has_large_step_mod(total, k, d, step_cap(total, k))
    }
}

proof fn lemma_mod_add(x: int, y: int)
    requires
        0 <= x,
        0 <= y,
    ensures
        ((x % modulus()) + (y % modulus())) % modulus() == (x + y) % modulus(),
{
}

proof fn lemma_mod_range(x: int)
    requires
        0 <= x,
    ensures
        0 <= x % modulus() < modulus(),
{
}

proof fn lemma_count_no_large_step_nonnegative(total: int, k: int, d: int, step: int)
    requires
        0 < total,
        1 <= d <= k,
        0 <= step <= step_cap(total, k),
    ensures
        0 <= count_no_large_step(total, k, d, step),
    decreases total, step,
{
    if step > 0 {
        lemma_count_no_large_step_nonnegative(total, k, d, step - 1);
        if step < d {
            let rem = total - step;
            if rem > 0 {
                lemma_count_no_large_step_nonnegative(rem, k, d, step_cap(rem, k));
            }
        }
    }
}

proof fn lemma_count_has_large_step_nonnegative(total: int, k: int, d: int, step: int)
    requires
        0 < total,
        1 <= d <= k,
        0 <= step <= step_cap(total, k),
    ensures
        0 <= count_has_large_step(total, k, d, step),
    decreases total, step,
{
    if step > 0 {
        lemma_count_has_large_step_nonnegative(total, k, d, step - 1);
        if step < d {
            let rem = total - step;
            if rem > 0 {
                lemma_count_has_large_step_nonnegative(rem, k, d, step_cap(rem, k));
            }
        } else {
            let rem = total - step;
            if rem > 0 {
                lemma_count_no_large_step_nonnegative(rem, k, d, step_cap(rem, k));
                lemma_count_has_large_step_nonnegative(rem, k, d, step_cap(rem, k));
            }
        }
    }
}

proof fn lemma_count_no_large_step_mod_correct(total: int, k: int, d: int, step: int)
    requires
        0 < total,
        1 <= d <= k,
        0 <= step <= step_cap(total, k),
    ensures
        count_no_large_step_mod(total, k, d, step) == count_no_large_step(total, k, d, step) % modulus(),
        0 <= count_no_large_step_mod(total, k, d, step) < modulus(),
    decreases total, step,
{
    if step > 0 {
        lemma_count_no_large_step_mod_correct(total, k, d, step - 1);
        if step < d {
            let rem = total - step;
            lemma_count_no_large_step_nonnegative(total, k, d, step - 1);
            if rem == 0 {
                lemma_mod_add(count_no_large_step(total, k, d, step - 1), 1);
                lemma_mod_range(count_no_large_step(total, k, d, step - 1) + 1);
            } else {
                lemma_count_no_large_step_mod_correct(rem, k, d, step_cap(rem, k));
                lemma_count_no_large_step_nonnegative(rem, k, d, step_cap(rem, k));
                lemma_mod_add(
                    count_no_large_step(total, k, d, step - 1),
                    count_no_large_step(rem, k, d, step_cap(rem, k)),
                );
                lemma_mod_range(
                    count_no_large_step(total, k, d, step - 1)
                        + count_no_large_step(rem, k, d, step_cap(rem, k)),
                );
            }
        }
    }
}

proof fn lemma_count_has_large_step_mod_correct(total: int, k: int, d: int, step: int)
    requires
        0 < total,
        1 <= d <= k,
        0 <= step <= step_cap(total, k),
    ensures
        count_has_large_step_mod(total, k, d, step) == count_has_large_step(total, k, d, step) % modulus(),
        0 <= count_has_large_step_mod(total, k, d, step) < modulus(),
    decreases total, step,
{
    if step > 0 {
        lemma_count_has_large_step_mod_correct(total, k, d, step - 1);
        lemma_count_has_large_step_nonnegative(total, k, d, step - 1);
        if step < d {
            let rem = total - step;
            if rem > 0 {
                lemma_count_has_large_step_mod_correct(rem, k, d, step_cap(rem, k));
                lemma_count_has_large_step_nonnegative(rem, k, d, step_cap(rem, k));
                lemma_mod_add(
                    count_has_large_step(total, k, d, step - 1),
                    count_has_large_step(rem, k, d, step_cap(rem, k)),
                );
                lemma_mod_range(
                    count_has_large_step(total, k, d, step - 1)
                        + count_has_large_step(rem, k, d, step_cap(rem, k)),
                );
            }
        } else {
            let rem = total - step;
            if rem == 0 {
                lemma_mod_add(count_has_large_step(total, k, d, step - 1), 1);
                lemma_mod_range(count_has_large_step(total, k, d, step - 1) + 1);
            } else {
                lemma_count_no_large_step_mod_correct(rem, k, d, step_cap(rem, k));
                lemma_count_has_large_step_mod_correct(rem, k, d, step_cap(rem, k));
                lemma_count_no_large_step_nonnegative(rem, k, d, step_cap(rem, k));
                lemma_count_has_large_step_nonnegative(rem, k, d, step_cap(rem, k));
                lemma_mod_add(
                    count_has_large_step(total, k, d, step - 1),
                    count_no_large_step(rem, k, d, step_cap(rem, k)),
                );
                lemma_mod_add(
                    count_has_large_step(total, k, d, step - 1)
                        + count_no_large_step(rem, k, d, step_cap(rem, k)),
                    count_has_large_step(rem, k, d, step_cap(rem, k)),
                );
                lemma_mod_range(
                    ((count_has_large_step(total, k, d, step - 1)
                        + count_no_large_step(rem, k, d, step_cap(rem, k))) % modulus())
                        + count_has_large_step_mod(rem, k, d, step_cap(rem, k)),
                );
            }
        }
    }
}

proof fn lemma_count_no_large_mod_correct(total: int, k: int, d: int)
    requires
        0 <= total,
        1 <= d <= k,
    ensures
        count_no_large_mod(total, k, d) == count_no_large(total, k, d) % modulus(),
        0 <= count_no_large_mod(total, k, d) < modulus(),
{
    if total > 0 {
        lemma_count_no_large_step_mod_correct(total, k, d, step_cap(total, k));
    }
}

proof fn lemma_count_has_large_mod_correct(total: int, k: int, d: int)
    requires
        0 <= total,
        1 <= d <= k,
    ensures
        count_has_large_mod(total, k, d) == count_has_large(total, k, d) % modulus(),
        0 <= count_has_large_mod(total, k, d) < modulus(),
{
    if total > 0 {
        lemma_count_has_large_step_mod_correct(total, k, d, step_cap(total, k));
    }
}

impl Solution {
    fn add_mod(x: i32, y: i32) -> (res: i32)
        requires
            0 <= x < modulus(),
            0 <= y < modulus(),
        ensures
            0 <= res < modulus(),
            res as int == ((x as int) + (y as int)) % modulus(),
    {
        let sum = x + y;
        if sum >= 1_000_000_007i32 {
            sum - 1_000_000_007i32
        } else {
            sum
        }
    }

    pub fn count_k_tree_paths(n: i32, k: i32, d: i32) -> (result: i32)
        requires
            1 <= n <= 100,
            1 <= d <= k <= 100,
        ensures
            0 <= result < modulus(),
            result as int == count_has_large(n as int, k as int, d as int) % modulus(),
    {
        let mut no_large = Vec::new();
        no_large.push(1);
        let mut has_large = Vec::new();
        has_large.push(0);
        let mut total = 1usize;
        while total <= n as usize
            invariant
                1 <= n <= 100,
                1 <= d <= k <= 100,
                1 <= total <= n as usize + 1,
                no_large.len() == total,
                has_large.len() == total,
                forall|j: int| 0 <= j < no_large.len() ==> 0 <= #[trigger] no_large@[j] < modulus()
                    && no_large@[j] as int == count_no_large_mod(j, k as int, d as int),
                forall|j: int| 0 <= j < has_large.len() ==> 0 <= #[trigger] has_large@[j] < modulus()
                    && has_large@[j] as int == count_has_large_mod(j, k as int, d as int),
            decreases n as usize + 1 - total,
        {
            let current = total;
            let upper = if current < k as usize { current } else { k as usize };
            let mut small = 0i32;
            let mut large = 0i32;
            let mut step = 1usize;
            while step <= upper
                invariant
                    1 <= d <= k <= 100,
                    1 <= step <= upper + 1,
                    upper <= current <= 100,
                    upper == step_cap(current as int, k as int),
                    current == total,
                    1 <= current,
                    no_large.len() == current,
                    has_large.len() == current,
                    0 <= small < modulus(),
                    0 <= large < modulus(),
                    small as int == count_no_large_step_mod(current as int, k as int, d as int, step as int - 1),
                    large as int == count_has_large_step_mod(current as int, k as int, d as int, step as int - 1),
                    forall|j: int| 0 <= j < no_large.len() ==> 0 <= #[trigger] no_large@[j] < modulus()
                        && no_large@[j] as int == count_no_large_mod(j, k as int, d as int),
                    forall|j: int| 0 <= j < has_large.len() ==> 0 <= #[trigger] has_large@[j] < modulus()
                        && has_large@[j] as int == count_has_large_mod(j, k as int, d as int),
                decreases upper + 1 - step,
            {
                let prev_small = no_large[current - step];
                let prev_large = has_large[current - step];
                if step < d as usize {
                    small = Self::add_mod(small, prev_small);
                    large = Self::add_mod(large, prev_large);
                    proof {
                        let rem = (current - step) as int;
                        assert(0 <= rem < no_large.len());
                        assert(prev_small as int == count_no_large_mod(rem, k as int, d as int));
                        assert(prev_large as int == count_has_large_mod(rem, k as int, d as int));
                        if rem == 0 {
                            assert(count_no_large_mod(rem, k as int, d as int) == 1);
                            assert(count_has_large_mod(rem, k as int, d as int) == 0);
                        } else {
                            assert(count_no_large_mod(rem, k as int, d as int)
                                == count_no_large_step_mod(rem, k as int, d as int, step_cap(rem, k as int)));
                            assert(count_has_large_mod(rem, k as int, d as int)
                                == count_has_large_step_mod(rem, k as int, d as int, step_cap(rem, k as int)));
                        }
                        assert(count_no_large_step_mod(current as int, k as int, d as int, step as int)
                            == (count_no_large_step_mod(current as int, k as int, d as int, step as int - 1)
                                + count_no_large_mod(rem, k as int, d as int)) % modulus()) by {
                            if rem == 0 {
                            }
                        }
                        assert(count_has_large_step_mod(current as int, k as int, d as int, step as int)
                            == (count_has_large_step_mod(current as int, k as int, d as int, step as int - 1)
                                + count_has_large_mod(rem, k as int, d as int)) % modulus()) by {
                            if rem == 0 {
                                assert(count_has_large_mod(rem, k as int, d as int) == 0);
                            }
                        }
                    }
                } else {
                    large = Self::add_mod(large, prev_small);
                    large = Self::add_mod(large, prev_large);
                    proof {
                        let rem = (current - step) as int;
                        assert(0 <= rem < no_large.len());
                        assert(prev_small as int == count_no_large_mod(rem, k as int, d as int));
                        assert(prev_large as int == count_has_large_mod(rem, k as int, d as int));
                        if rem == 0 {
                            assert(count_no_large_mod(rem, k as int, d as int) == 1);
                            assert(count_has_large_mod(rem, k as int, d as int) == 0);
                        } else {
                            assert(count_no_large_mod(rem, k as int, d as int)
                                == count_no_large_step_mod(rem, k as int, d as int, step_cap(rem, k as int)));
                            assert(count_has_large_mod(rem, k as int, d as int)
                                == count_has_large_step_mod(rem, k as int, d as int, step_cap(rem, k as int)));
                        }
                        assert(count_has_large_step_mod(current as int, k as int, d as int, step as int)
                            == ((count_has_large_step_mod(current as int, k as int, d as int, step as int - 1)
                                + count_no_large_mod(rem, k as int, d as int)) % modulus()
                                + count_has_large_mod(rem, k as int, d as int)) % modulus()) by {
                            if rem == 0 {
                            }
                        }
                    }
                }
                step += 1;
            }
            proof {
                if current < k as usize {
                    assert(upper as int == current as int);
                    assert(step_cap(current as int, k as int) == current as int);
                } else {
                    assert(upper as int == k as int);
                    assert(step_cap(current as int, k as int) == k as int);
                }
                assert(step == upper + 1);
                assert(step as int - 1 == step_cap(current as int, k as int));
                assert(small as int == count_no_large_mod(current as int, k as int, d as int));
                assert(large as int == count_has_large_mod(current as int, k as int, d as int));
            }
            no_large.push(small);
            has_large.push(large);
            proof {
                assert(no_large.len() == current + 1);
                assert(has_large.len() == current + 1);
                assert(no_large@[current as int] == small);
                assert(has_large@[current as int] == large);
                assert forall|j: int| 0 <= j < no_large.len() implies
                    0 <= #[trigger] no_large@[j] < modulus()
                        && no_large@[j] as int == count_no_large_mod(j, k as int, d as int) by {
                    if j < current as int {
                    } else {
                        assert(j == current as int);
                    }
                }
                assert forall|j: int| 0 <= j < has_large.len() implies
                    0 <= #[trigger] has_large@[j] < modulus()
                        && has_large@[j] as int == count_has_large_mod(j, k as int, d as int) by {
                    if j < current as int {
                    } else {
                        assert(j == current as int);
                    }
                }
            }
            total += 1;
        }
        proof {
            lemma_count_has_large_mod_correct(n as int, k as int, d as int);
            assert(total == n as usize + 1);
            assert(has_large@[n as int] as int == count_has_large_mod(n as int, k as int, d as int));
        }
        has_large[n as usize]
    }
}

}
