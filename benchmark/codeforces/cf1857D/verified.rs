use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn diff(a: Seq<i32>, b: Seq<i32>, i: int) -> int {
    a[i] as int - b[i] as int
}

pub open spec fn is_max_index(a: Seq<i32>, b: Seq<i32>, j: int) -> bool {
    0 <= j < a.len() && forall|m: int| 0 <= m < a.len() ==> diff(a, b, j) >= #[trigger] diff(a, b, m)
}

pub open spec fn sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] < s[j]
}

pub struct Solution;

impl Solution {
    pub fn strong_vertices(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
        requires
            2 <= a.len() <= 200_000,
            a.len() == b.len(),
            forall|j: int| 0 <= j < a.len() ==> -1_000_000_000 <= #[trigger] a[j] <= 1_000_000_000,
            forall|j: int| 0 <= j < b.len() ==> -1_000_000_000 <= #[trigger] b[j] <= 1_000_000_000,
        ensures
            result.len() >= 1,
            forall|k: int| 0 <= k < result.len() ==> 1 <= #[trigger] result[k] <= a.len() as i32
                && is_max_index(a@, b@, (result[k] - 1) as int),
            forall|j: int| 0 <= j < a.len() && is_max_index(a@, b@, j)
                ==> exists|k: int| 0 <= k < result.len() && #[trigger] result[k] == (j + 1) as i32,
            sorted(result@),
    {
        let n = a.len();
        let mut max_d: i32 = a[0] - b[0];
        let mut result: Vec<i32> = Vec::new();
        result.push(1);
        proof {
            assert(sorted(result@));
            assert(forall|m: int| 0 <= m < 1 && diff(a@, b@, m) == max_d as int
                ==> exists|k: int| 0 <= k < result.len() && result[k] == (m + 1) as i32) by {
                assert forall|m: int| 0 <= m < 1 && diff(a@, b@, m) == max_d as int
                    implies exists|k: int| 0 <= k < result.len() && result[k] == (m + 1) as i32 by {
                    assert(m == 0);
                    assert(0 <= 0 < result.len());
                    assert(result[0] == 1);
                }
            };
        }

        let mut i: usize = 1;
        while i < n
            invariant
                1 <= i <= n,
                n == a.len(),
                n == b.len(),
                2 <= n <= 200_000,
                forall|j: int| 0 <= j < n ==> -1_000_000_000 <= #[trigger] a[j] <= 1_000_000_000,
                forall|j: int| 0 <= j < n ==> -1_000_000_000 <= #[trigger] b[j] <= 1_000_000_000,
                result.len() >= 1,
                forall|k: int| 0 <= k < result.len() ==> 1 <= #[trigger] result[k] <= i as int,
                forall|k: int| 0 <= k < result.len() ==> diff(a@, b@, (result[k] - 1) as int) == max_d as int,
                forall|m: int| 0 <= m < i as int ==> diff(a@, b@, m) <= max_d as int,
                forall|m: int| 0 <= m < i as int && diff(a@, b@, m) == max_d as int
                    ==> exists|k: int| 0 <= k < result.len() && #[trigger] result[k] == (m + 1) as i32,
                sorted(result@),
            decreases n - i,
        {
            let d = a[i] - b[i];
            if d > max_d {
                let old_max_d = max_d;
                max_d = d;
                result = Vec::new();
                result.push((i + 1) as i32);
                proof {
                    assert(diff(a@, b@, i as int) == d as int);
                    assert(d as int > old_max_d as int);
                    assert forall|m: int| 0 <= m < i as int implies diff(a@, b@, m) < d as int by {
                        assert(diff(a@, b@, m) <= old_max_d as int);
                    };
                    assert(forall|m: int| 0 <= m < i as int + 1 && diff(a@, b@, m) == max_d as int
                        ==> exists|k: int| 0 <= k < result.len() && result[k] == (m + 1) as i32) by {
                        assert forall|m: int| 0 <= m < i as int + 1 && diff(a@, b@, m) == max_d as int
                            implies exists|k: int| 0 <= k < result.len() && result[k] == (m + 1) as i32 by {
                            if m < i as int {
                                assert(diff(a@, b@, m) < d as int);
                                assert(false);
                            } else {
                                assert(m == i as int);
                                assert(0 <= 0 < result.len());
                                assert(result[0] == (i + 1) as i32);
                            }
                        }
                    };
                    assert(sorted(result@));
                }
            } else if d == max_d {
                let ghost old_result = result@;
                result.push((i + 1) as i32);
                proof {
                    assert(result@.drop_last() == old_result);
                    assert(sorted(old_result));
                    assert(result@[result@.len() - 1] == (i + 1) as i32);
                    assert forall|p: int| 0 <= p < result@.len() - 1 implies #[trigger] result@[p] < result@[result@.len() - 1] by {
                        assert(result@[p] <= i as int);
                        assert((i + 1) as int == (i as int) + 1);
                    };
                    assert(forall|m: int| 0 <= m < i as int + 1 && diff(a@, b@, m) == max_d as int
                        ==> exists|k: int| 0 <= k < result.len() && result[k] == (m + 1) as i32) by {
                        assert forall|m: int| 0 <= m < i as int + 1 && diff(a@, b@, m) == max_d as int
                            implies exists|k: int| 0 <= k < result.len() && result[k] == (m + 1) as i32 by {
                            if m < i as int {
                                assert(exists|k: int| 0 <= k < old_result.len() && old_result[k] == (m + 1) as i32);
                                let k0 = choose|k: int| 0 <= k < old_result.len() && old_result[k] == (m + 1) as i32;
                                assert(0 <= k0 < result.len());
                                assert(result[k0] == (m + 1) as i32);
                            } else {
                                assert(m == i as int);
                                assert(0 <= result.len() - 1 < result.len());
                                assert(result[result.len() - 1] == (i + 1) as i32);
                            }
                        }
                    };
                    assert(sorted(result@));
                }
            } else {
                proof {
                    assert(d < max_d);
                    assert(forall|m: int| 0 <= m < i as int + 1 && diff(a@, b@, m) == max_d as int
                        ==> exists|k: int| 0 <= k < result.len() && result[k] == (m + 1) as i32) by {
                        assert forall|m: int| 0 <= m < i as int + 1 && diff(a@, b@, m) == max_d as int
                            implies exists|k: int| 0 <= k < result.len() && result[k] == (m + 1) as i32 by {
                            if m < i as int {
                                assert(exists|k: int| 0 <= k < result.len() && result[k] == (m + 1) as i32);
                            } else {
                                assert(m == i as int);
                                assert(diff(a@, b@, m) == d as int);
                                assert((d as int) < (max_d as int));
                                assert(false);
                            }
                        }
                    };
                }
            }
            i = i + 1;
        }

        proof {
            assert(i == n);
            assert(forall|k: int| 0 <= k < result.len()
                ==> 1 <= result[k] <= a.len() as i32 && is_max_index(a@, b@, (result[k] - 1) as int)) by {
                assert forall|k: int| 0 <= k < result.len()
                    implies 1 <= result[k] <= a.len() as i32 && is_max_index(a@, b@, (result[k] - 1) as int) by {
                    let j = (result[k] - 1) as int;
                    assert(0 <= j < n as int);
                    assert(1 <= result[k] <= n as i32);
                    assert(diff(a@, b@, j) == max_d as int);
                    assert forall|m: int| 0 <= m < n as int implies diff(a@, b@, j) >= diff(a@, b@, m) by {
                        assert(diff(a@, b@, m) <= max_d as int);
                    }
                }
            };

            assert(forall|j: int| 0 <= j < a.len() && is_max_index(a@, b@, j)
                ==> exists|k: int| 0 <= k < result.len() && result[k] == (j + 1) as i32) by {
                assert forall|j: int| 0 <= j < a.len() && is_max_index(a@, b@, j)
                    implies exists|k: int| 0 <= k < result.len() && result[k] == (j + 1) as i32 by {
                    assert(diff(a@, b@, j) <= max_d as int);
                    assert(diff(a@, b@, j) >= max_d as int) by {
                        assert(0 <= result[0] - 1 < n as i32);
                        let r0 = (result[0] - 1) as int;
                        assert(0 <= r0 < n as int);
                        assert(diff(a@, b@, r0) == max_d as int);
                    }
                    assert(diff(a@, b@, j) == max_d as int);
                    assert(exists|k: int| 0 <= k < result.len() && result[k] == (j + 1) as i32);
                }
            };

            assert(sorted(result@));
        }

        result
    }
}

}
