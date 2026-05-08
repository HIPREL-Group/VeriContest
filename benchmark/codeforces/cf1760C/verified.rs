use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn valid_advantage(s: Seq<i64>, i: int, d: int) -> bool {
    exists|j: int| {
        &&& 0 <= j < s.len()
        &&& j != i
        &&& d == s[i] as int - s[j] as int
        &&& forall|k: int| 0 <= k < s.len() && k != i ==> s[k] as int <= #[trigger] s[j] as int
    }
}

pub struct Solution;

impl Solution {
    pub fn advantages(s: Vec<i64>) -> (result: Vec<i64>)
        requires
            2 <= s.len() <= 200_000,
            forall|i: int| 0 <= i < s.len() ==> 1 <= #[trigger] s[i] <= 1_000_000_000,
        ensures
            result.len() == s.len(),
            forall|i: int| 0 <= i < s.len() ==> valid_advantage(s@, i, result[i] as int),
    {
        let n = s.len();
        let mut max1: i64 = s[0];
        let mut idx1: usize = 0;
        let mut max2: i64 = s[1];
        let mut idx2: usize = 1;

        if max2 > max1 {
            let tv = max1;
            let ti = idx1;
            max1 = max2;
            idx1 = idx2;
            max2 = tv;
            idx2 = ti;
        }

        assert(idx1 != idx2);
        assert(s[idx1 as int] == max1);
        assert(s[idx2 as int] == max2);
        assert(max2 <= max1);
        assert forall|k: int| 0 <= k < 2 implies s[k] <= max1 by {
            if k == idx1 as int {
                assert(s[k] == max1);
            } else {
                assert(k == idx2 as int);
                assert(s[k] == max2);
                assert(max2 <= max1);
            }
        };
        assert forall|k: int| 0 <= k < 2 && k != idx1 as int implies s[k] <= max2 by {
            assert(k == idx2 as int);
            assert(s[k] == max2);
        };

        let mut t: usize = 2;
        while t < n
            invariant
                n == s.len(),
                2 <= n <= 200_000,
                2 <= t <= n,
                0 <= idx1 < t,
                0 <= idx2 < t,
                idx1 != idx2,
                s[idx1 as int] == max1,
                s[idx2 as int] == max2,
                max2 <= max1,
                forall|q: int| 0 <= q < n as int ==> 1 <= #[trigger] s[q] <= 1_000_000_000,
                forall|k: int| 0 <= k < t as int ==> s[k] <= max1,
                forall|k: int| 0 <= k < t as int && k != idx1 as int ==> s[k] <= max2,
            decreases n - t,
        {
            if s[t] > max1 {
                max2 = max1;
                idx2 = idx1;
                max1 = s[t];
                idx1 = t;
                proof {
                    assert(max2 <= max1);
                    assert forall|k: int| 0 <= k < t as int + 1 implies s[k] <= max1 by {
                        if k == t as int {
                            assert(s[k] == max1);
                        } else {
                            assert(k < t as int);
                            assert(s[k] <= s[idx2 as int]);
                            assert(s[idx2 as int] == max2);
                            assert(max2 <= max1);
                        }
                    };
                    assert forall|k: int| 0 <= k < t as int + 1 && k != idx1 as int implies s[k] <= max2 by {
                        assert(k < t as int);
                        assert(s[k] <= s[idx2 as int]);
                        assert(s[idx2 as int] == max2);
                    };
                }
            } else if s[t] > max2 {
                max2 = s[t];
                idx2 = t;
                proof {
                    assert(max2 <= max1);
                    assert forall|k: int| 0 <= k < t as int + 1 implies s[k] <= max1 by {
                        if k == t as int {
                            assert(s[k] == max2);
                            assert(max2 <= max1);
                        } else {
                            assert(k < t as int);
                            assert(s[k] <= max1);
                        }
                    };
                    assert forall|k: int| 0 <= k < t as int + 1 && k != idx1 as int implies s[k] <= max2 by {
                        if k == t as int {
                            assert(s[k] == max2);
                        } else {
                            assert(k < t as int);
                            assert(s[k] <= s[idx2 as int]);
                            assert(s[idx2 as int] == max2);
                        }
                    };
                }
            } else {
                proof {
                    assert(s[t as int] <= max2);
                    assert forall|k: int| 0 <= k < t as int + 1 implies s[k] <= max1 by {
                        if k == t as int {
                            assert(s[k] <= max2);
                            assert(max2 <= max1);
                        } else {
                            assert(k < t as int);
                            assert(s[k] <= max1);
                        }
                    };
                    assert forall|k: int| 0 <= k < t as int + 1 && k != idx1 as int implies s[k] <= max2 by {
                        if k == t as int {
                            assert(s[k] <= max2);
                        } else {
                            assert(k < t as int);
                            assert(s[k] <= max2);
                        }
                    };
                }
            }
            t = t + 1;
        }

        assert(t == n);
        assert forall|k: int| 0 <= k < n as int implies s[k] <= max1 by {
            assert(k < t as int);
        };
        assert forall|k: int| 0 <= k < n as int && k != idx1 as int implies s[k] <= max2 by {
            assert(k < t as int);
        };

        let mut result: Vec<i64> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n
            invariant
                n == s.len(),
                2 <= n <= 200_000,
                0 <= i <= n,
                0 <= idx1 < n,
                0 <= idx2 < n,
                idx1 != idx2,
                s[idx1 as int] == max1,
                s[idx2 as int] == max2,
                max2 <= max1,
                result.len() == i,
                forall|q: int| 0 <= q < n as int ==> 1 <= #[trigger] s[q] <= 1_000_000_000,
                forall|k: int| 0 <= k < n as int ==> s[k] <= max1,
                forall|k: int| 0 <= k < n as int && k != idx1 as int ==> s[k] <= max2,
                forall|p: int| 0 <= p < i as int ==> valid_advantage(s@, p, result[p] as int),
            decreases n - i,
        {
            let best: i64;
            let witness: usize;
            if i == idx1 {
                best = max2;
                witness = idx2;
            } else {
                best = max1;
                witness = idx1;
            }

            assert(0 <= witness < n);
            assert(witness != i);
            assert(s[witness as int] == best);
            assert forall|k: int| 0 <= k < n as int && k != i as int implies s[k] <= best by {
                if i == idx1 {
                    assert(best == max2);
                    assert(k != idx1 as int);
                    assert(s[k] <= max2);
                } else {
                    assert(best == max1);
                    assert(s[k] <= max1);
                }
            }

            assert(1 <= s[i as int] <= 1_000_000_000) by {
                assert(0 <= i as int);
                assert((i as int) < (s.len() as int));
            }
            assert(1 <= s[witness as int] <= 1_000_000_000) by {
                assert(0 <= witness as int);
                assert((witness as int) < (s.len() as int));
            }
            assert(best == s[witness as int]);
            assert(1 <= best <= 1_000_000_000);
            assert(-1_000_000_000i64 <= s[i as int] - best <= 1_000_000_000i64);
            result.push(s[i] - best);
            proof {
                let p = i as int;
                let w = witness as int;
                assert(0 <= w < s.len());
                assert(w != p);
                assert(result[p] == s[p] - best);
                assert(result[p] as int == s[p] as int - best as int);
                assert(result[p] as int == s[p] as int - s[w] as int);
                assert(forall|k: int| 0 <= k < s.len() && k != p ==> s[k] as int <= s[w] as int);
                assert(valid_advantage(s@, p, result[p] as int));
            }
            i = i + 1;
        }

        proof {
            assert(!(i < n));
            assert(i == n);
            assert(result.len() == s.len());
            assert(forall|p: int| 0 <= p < s.len() ==> valid_advantage(s@, p, result[p] as int));
        }

        result
    }
}

}
