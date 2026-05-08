use vstd::prelude::*;
use vstd::arithmetic::div_mod::lemma_div_is_ordered;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn removable_pairs_prefix(s: Seq<i64>, n: int, pairs: int) -> bool
        recommends
            0 <= pairs <= n,
            n == s.len(),
    {
        forall|k: int| 0 <= k < pairs ==> #[trigger] s[k] + s[n - 1 - k] == 1
    }

    pub open spec fn feasible_original_len(s: Seq<i64>, original_len: int) -> bool
        recommends
            s.len() >= 1,
    {
        let n = s.len() as int;
        &&& 0 <= original_len <= n
        &&& (n - original_len) % 2 == 0
        &&& Self::removable_pairs_prefix(s, n, (n - original_len) / 2)
    }

    pub fn shortest_original(n: usize, s: Vec<i64>) -> (result: usize)
        requires
            n >= 1,
            s.len() == n,
            forall|i: int| 0 <= i < n as int ==> (#[trigger] s@[i] == 0 || s@[i] == 1),
        ensures
            Self::feasible_original_len(s@, result as int),
            forall|r2: int| 0 <= r2 < result as int ==> !Self::feasible_original_len(s@, r2),
    {
        let mut left: usize = 0;
        let mut right: usize = n - 1;
        while left < right
            invariant
                left + right == n - 1,
                left as int <= right as int + 1,
                left < n,
                right < n,
                s.len() == n,
                n >= 1,
                forall|i: int| 0 <= i < n as int ==> (#[trigger] s@[i] == 0 || s@[i] == 1),
                forall|k: int| 0 <= k < left as int ==>
                    (#[trigger] s@[k]) + s@[n as int - 1 - k] == 1,
            decreases n - left,
        {
            if s[left] + s[right] != 1 {
                proof {
                    let res = right - left + 1;
                    assert(res as int == right as int - left as int + 1);
                    assert(0 <= res as int <= n as int);
                    assert(n as int - res as int == 2 * left as int);
                    assert((2 * left as int) % 2 == 0) by (nonlinear_arith)
                        requires left as int >= 0;
                    assert((n as int - res as int) % 2 == 0);
                    assert((n as int - res as int) / 2 == left as int) by (nonlinear_arith)
                        requires
                            n as int - res as int == 2 * left as int,
                            left as int >= 0;
                    assert(Self::removable_pairs_prefix(s@, n as int, left as int));
                    assert(Self::feasible_original_len(s@, res as int));
                    assert forall|r2: int| 0 <= r2 < res as int implies !Self::feasible_original_len(s@, r2) by {
                        if 0 <= r2 < res as int {
                            if Self::feasible_original_len(s@, r2) {
                                let p2 = (n as int - r2) / 2;
                                assert((n as int - r2) % 2 == 0);
                                assert(n as int - r2 >= 2 * left as int + 1) by (nonlinear_arith)
                                    requires
                                        r2 < res as int,
                                        n as int - res as int == 2 * left as int,
                                {
                                }
                                assert(n as int - r2 >= 2 * left as int + 2) by (nonlinear_arith)
                                    requires
                                        (n as int - r2) % 2 == 0,
                                        n as int - r2 >= 2 * left as int + 1,
                                {
                                }
                                lemma_div_is_ordered(2 * left as int + 2, n as int - r2, 2);
                                assert((2 * left as int + 2) / 2 <= (n as int - r2) / 2);
                                assert((2 * left as int + 2) / 2 == left as int + 1) by (nonlinear_arith)
                                    requires
                                        left as int >= 0,
                                {
                                }
                                assert(p2 >= left as int + 1);
                                assert(0 <= (left as int));
                                assert((left as int) < p2);
                                assert(Self::removable_pairs_prefix(s@, n as int, p2));
                                assert(s@[left as int] + s@[n as int - 1 - left as int] == 1);
                                assert(n as int - 1 - left as int == right as int) by (nonlinear_arith)
                                    requires
                                        left as int + right as int == n as int - 1,
                                {
                                }
                                assert(s@[left as int] + s@[right as int] == 1);
                                assert(s@[left as int] + s@[right as int] != 1) by {
                                    assert(s[left as int] + s[right as int] != 1);
                                }
                                assert(false);
                            }
                        }
                    };
                }
                return right - left + 1;
            }
            left += 1;
            right -= 1;
        }
        if left > right {
            proof {
                assert(left as int == right as int + 1);
                assert(n as int == 2 * left as int);
                assert(n as int % 2 == 0) by (nonlinear_arith)
                    requires n as int == 2 * left as int;
                assert(n as int / 2 == left as int) by (nonlinear_arith)
                    requires n as int == 2 * left as int, left as int >= 0;
                assert(Self::removable_pairs_prefix(s@, n as int, left as int));
                assert(Self::feasible_original_len(s@, 0));
                assert forall|r2: int| 0 <= r2 < 0 implies !Self::feasible_original_len(s@, r2) by {
                };
            }
            0
        } else {
            proof {
                assert(left == right);
                assert(n as int - 1 == 2 * left as int);
                assert((n as int - 1) % 2 == 0) by (nonlinear_arith)
                    requires n as int - 1 == 2 * left as int;
                assert((n as int - 1) / 2 == left as int) by (nonlinear_arith)
                    requires n as int - 1 == 2 * left as int, left as int >= 0;
                assert(Self::removable_pairs_prefix(s@, n as int, left as int));
                assert(Self::feasible_original_len(s@, 1));
                assert forall|r2: int| 0 <= r2 < 1 implies !Self::feasible_original_len(s@, r2) by {
                    if 0 <= r2 < 1 {
                        assert(r2 == 0);
                        assert(n as int % 2 == 1) by (nonlinear_arith)
                            requires n as int - 1 == 2 * left as int;
                        assert((n as int - r2) % 2 != 0);
                        assert(!Self::feasible_original_len(s@, r2));
                    }
                };
            }
            right - left + 1
        }
    }
}

}
