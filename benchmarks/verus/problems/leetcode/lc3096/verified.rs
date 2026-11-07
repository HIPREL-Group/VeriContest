use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn level_score(x: i32) -> int {
        if x == 1 { 1 } else { -1 }
    }

    pub open spec fn prefix_score(possible: Seq<i32>, end: int) -> int
        recommends
            0 <= end <= possible.len(),
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::prefix_score(possible, end - 1) + Self::level_score(possible[end - 1])
        }
    }

    pub open spec fn alice_wins_after_k(possible: Seq<i32>, k: int) -> bool {
        &&& 1 <= k < possible.len()
        &&& 2 * Self::prefix_score(possible, k) > Self::prefix_score(possible, possible.len() as int)
    }

    proof fn lemma_prefix_step(possible: Seq<i32>, i: int)
        requires
            0 <= i < possible.len(),
        ensures
            Self::prefix_score(possible, i + 1) == Self::prefix_score(possible, i) + Self::level_score(possible[i]),
    {
    }

    pub fn minimum_levels(possible: Vec<i32>) -> (result: i32)
        requires
            2 <= possible.len() <= 100000,
            forall |i: int| 0 <= i < possible.len() ==> (#[trigger] possible[i] == 0 || #[trigger] possible[i] == 1),
        ensures
            result == -1 ==> forall |k: int| 1 <= k < possible.len() ==> !Self::alice_wins_after_k(possible@, k),
            result != -1 ==> (
                1 <= result as int && (result as int) < possible.len()
                && Self::alice_wins_after_k(possible@, result as int)
                && forall |k: int| 1 <= k < result as int ==> !Self::alice_wins_after_k(possible@, k)
            ),
    {
        let n = possible.len();
        let mut total: i64 = 0;
        let mut i: usize = 0;

        while i < n
            invariant
                n == possible.len(),
                2 <= n <= 100000,
                0 <= i <= n,
                forall |k: int| 0 <= k < n ==> (#[trigger] possible[k] == 0 || #[trigger] possible[k] == 1),
                total as int == Self::prefix_score(possible@, i as int),
                -(i as int) <= total as int <= i as int,
            decreases n - i,
        {
            let delta: i64 = if possible[i] == 1 { 1 } else { -1 };
            proof {
                Self::lemma_prefix_step(possible@, i as int);
                assert(delta as int == Self::level_score(possible@[i as int]));
            }
            total = total + delta;
            proof {
                assert(total as int == Self::prefix_score(possible@, i as int + 1));
                assert(-(i as int + 1) <= total as int <= i as int + 1);
            }
            i += 1;
        }

        let mut prefix: i64 = 0;
        i = 0;

        while i < n - 1
            invariant
                n == possible.len(),
                2 <= n <= 100000,
                0 <= i <= n - 1,
                forall |k: int| 0 <= k < n ==> (#[trigger] possible[k] == 0 || #[trigger] possible[k] == 1),
                total as int == Self::prefix_score(possible@, n as int),
                prefix as int == Self::prefix_score(possible@, i as int),
                -(i as int) <= prefix as int <= i as int,
                forall |k: int| 1 <= k <= i as int ==> !Self::alice_wins_after_k(possible@, k),
            decreases n - 1 - i,
        {
            let delta: i64 = if possible[i] == 1 { 1 } else { -1 };
            proof {
                Self::lemma_prefix_step(possible@, i as int);
                assert(delta as int == Self::level_score(possible@[i as int]));
            }
            prefix = prefix + delta;
            proof {
                assert(prefix as int == Self::prefix_score(possible@, i as int + 1));
                assert(-(i as int + 1) <= prefix as int <= i as int + 1);
            }
            if 2 * prefix > total {
                proof {
                    assert(1 <= i as int + 1 < n as int);
                    assert(Self::alice_wins_after_k(possible@, i as int + 1));
                    assert(forall |k: int| 1 <= k < i as int + 1 ==> !Self::alice_wins_after_k(possible@, k)) by {
                        assert forall |k: int| 1 <= k < i as int + 1 implies !Self::alice_wins_after_k(possible@, k) by {
                            assert(1 <= k <= i as int);
                        }
                    };
                    assert(i + 1 <= i32::MAX as usize);
                }
                return (i + 1) as i32;
            } else {
                proof {
                    assert(!(Self::alice_wins_after_k(possible@, i as int + 1)));
                }
            }
            i += 1;
        }

        proof {
            assert(i == n - 1);
            assert(forall |k: int| 1 <= k < possible.len() ==> !Self::alice_wins_after_k(possible@, k)) by {
                assert forall |k: int| 1 <= k < possible.len() implies !Self::alice_wins_after_k(possible@, k) by {
                    assert(1 <= k <= i as int);
                }
            };
        }

        -1
    }
}

}
