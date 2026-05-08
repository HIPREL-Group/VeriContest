use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn count_fixed_upto(p: Seq<i32>, hi: int) -> int
    decreases hi,
{
    if hi <= 0 {
        0
    } else {
        let idx = hi - 1;
        count_fixed_upto(p, hi - 1) + if (p[idx] as int) == idx + 1 {
            1int
        } else {
            0int
        }
    }
}

pub open spec fn min_swaps_spec(p: Seq<i32>) -> int {
    (count_fixed_upto(p, p.len() as int) + 1) / 2
}

proof fn lemma_count_fixed_extend(p: Seq<i32>, hi: int)
    requires
        0 < hi <= p.len(),
    ensures
        count_fixed_upto(p, hi) == count_fixed_upto(p, hi - 1) + if (p[hi - 1] as int) == hi {
            1int
        } else {
            0int
        },
    decreases hi,
{
    reveal_with_fuel(count_fixed_upto, 3);
    if hi > 1 {
        lemma_count_fixed_extend(p, hi - 1);
    }
    assert(count_fixed_upto(p, hi) == count_fixed_upto(p, hi - 1) + if (p[hi - 1] as int) == hi {
        1int
    } else {
        0int
    });
}

proof fn lemma_i32_div2_matches_int(c: i32)
    requires
        0 <= c <= 200_000,
    ensures
        (((c + 1) / 2) as int) == (c as int + 1) / 2,
{
}

pub struct Solution;

impl Solution {
    pub fn min_swaps(p: Vec<i32>) -> (result: i32)
        requires
            2 <= p.len() <= 100_000,
            forall|j: int|
                0 <= j < p.len() ==> 1 <= #[trigger] p[j] <= p.len() as int,
        ensures
            result as int == min_swaps_spec(p@),
    {
        let n = p.len();
        let mut c: i32 = 0;
        let mut i: usize = 0;
        proof {
            reveal_with_fuel(count_fixed_upto, 3);
            assert(c as int == count_fixed_upto(p@, 0));
        }
        while i < n
            invariant
                n == p.len(),
                2 <= n <= 100_000,
                i <= n,
                forall|j: int|
                    0 <= j < p.len() as int ==> 1 <= #[trigger] p[j] <= p.len() as int,
                c as int == count_fixed_upto(p@, i as int),
                0 <= c as int,
                c as int <= i as int,
                c as int <= n as int,
            decreases n - i,
        {
            proof {
                lemma_count_fixed_extend(p@, (i + 1) as int);
            }
            if p[i] == (i + 1) as i32 {
                c = c + 1;
                proof {
                    assert((p@[i as int] as int) == (i + 1) as int);
                    assert(count_fixed_upto(p@, (i + 1) as int) == count_fixed_upto(p@, i as int) + 1);
                    assert(c as int == count_fixed_upto(p@, (i + 1) as int));
                }
            } else {
                proof {
                    assert(!((p@[i as int] as int) == (i + 1) as int));
                    assert(count_fixed_upto(p@, (i + 1) as int) == count_fixed_upto(p@, i as int));
                    assert(c as int == count_fixed_upto(p@, (i + 1) as int));
                }
            }
            i = i + 1;
        }
        proof {
            assert(i == n);
            assert(c as int == count_fixed_upto(p@, n as int));
            assert(min_swaps_spec(p@) == (count_fixed_upto(p@, n as int) + 1) / 2);
        }
        proof {
            assert(0 <= c as int);
            assert(c as int <= n as int);
            lemma_i32_div2_matches_int(c);
        }
        (c + 1) / 2
    }
}

}
