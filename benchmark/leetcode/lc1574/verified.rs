use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_non_decreasing_range(s: Seq<i32>, lo: int, hi: int) -> bool {
        0 <= lo <= hi <= s.len() as int
        && forall|k: int| lo <= k < hi - 1 ==> #[trigger] s[k] <= s[k + 1]
    }

    pub open spec fn removal_works(s: Seq<i32>, l: int, r: int) -> bool {
        &&& 0 <= l <= r <= s.len() as int
        &&& Self::is_non_decreasing_range(s, 0, l)
        &&& Self::is_non_decreasing_range(s, r, s.len() as int)
        &&& (0 < l && r < s.len() as int ==> s[l - 1] <= s[r])
    }

    pub open spec fn no_bridge_before(s: Seq<i32>, p: int, start: int, j: int) -> bool {
        forall|q: int| start <= q < j ==> #[trigger] s[q] < s[p]
    }

    pub open spec fn processed_ok(s: Seq<i32>, start: int, p: int, best: int) -> bool {
        forall|q: int| start <= q < s.len() as int && s[p] <= #[trigger] s[q] ==> best <= q - p - 1
    }

    proof fn lemma_sorted_range_order(s: Seq<i32>, lo: int, hi: int, a: int, b: int)
        requires
            Self::is_non_decreasing_range(s, lo, hi),
            lo <= a <= b < hi,
        ensures
            s[a] <= s[b],
        decreases b - a,
    {
        if a < b {
            Self::lemma_sorted_range_order(s, lo, hi, a, b - 1);
            assert(s[a] <= s[b - 1]);
            assert(s[b - 1] <= s[b]);
        }
    }

    proof fn lemma_prefix_bound(s: Seq<i32>, cut: int, l: int)
        requires
            0 <= cut < s.len() as int - 1,
            Self::is_non_decreasing_range(s, 0, cut + 1),
            s[cut] > s[cut + 1],
            Self::is_non_decreasing_range(s, 0, l),
        ensures
            l <= cut + 1,
    {
        if cut + 1 < l {
            assert(s[cut] <= s[cut + 1]);
            assert(false);
        }
    }

    proof fn lemma_suffix_bound(s: Seq<i32>, cut: int, r: int)
        requires
            0 < cut < s.len() as int,
            Self::is_non_decreasing_range(s, cut, s.len() as int),
            s[cut - 1] > s[cut],
            Self::is_non_decreasing_range(s, r, s.len() as int),
        ensures
            cut <= r,
    {
        if r < cut {
            assert(s[cut - 1] <= s[cut]);
            assert(false);
        }
    }

    pub fn find_length_of_shortest_subarray(arr: Vec<i32>) -> (result: i32)
        requires
            1 <= arr.len() <= 100_000,
            forall|i: int| 0 <= i < arr.len() ==> 0 <= #[trigger] arr[i] <= 1_000_000_000,
        ensures
            0 <= result <= arr.len() as i32,
            exists|l: int, r: int| Self::removal_works(arr@, l, r) && result as int == r - l,
            forall|l: int, r: int| Self::removal_works(arr@, l, r) ==> result as int <= r - l,
    {
        let n = arr.len();
        let mut left: usize = 0;
        while left + 1 < n && arr[left] <= arr[left + 1]
            invariant
                n == arr.len(),
                1 <= n <= 100_000,
                0 <= left < n,
                forall|i: int| 0 <= i < n ==> 0 <= #[trigger] arr[i] <= 1_000_000_000,
                Self::is_non_decreasing_range(arr@, 0, left as int + 1),
            decreases n - left,
        {
            proof {
                assert(Self::is_non_decreasing_range(arr@, 0, left as int + 2)) by {
                    assert forall|k: int| 0 <= k < left as int + 1 implies #[trigger] arr@[k] <= arr@[k + 1] by {
                        if k < left as int {
                        } else {
                            assert(k == left as int);
                        }
                    };
                };
            }
            left = left + 1;
        }
        if left + 1 == n {
            proof {
                assert(Self::removal_works(arr@, 0, 0)) by {
                    assert(Self::is_non_decreasing_range(arr@, 0, n as int));
                };
                assert forall|l: int, r: int| Self::removal_works(arr@, l, r) implies 0 <= r - l by {
                };
            }
            return 0;
        }
        proof {
            assert(arr@[left as int] > arr@[left as int + 1]);
        }
        let mut right: usize = n - 1;
        while right > 0 && arr[right - 1] <= arr[right]
            invariant
                n == arr.len(),
                1 <= n <= 100_000,
                0 <= right < n,
                forall|i: int| 0 <= i < n ==> 0 <= #[trigger] arr[i] <= 1_000_000_000,
                Self::is_non_decreasing_range(arr@, right as int, n as int),
            decreases right,
        {
            proof {
                assert(Self::is_non_decreasing_range(arr@, right as int - 1, n as int)) by {
                    assert forall|k: int| right as int - 1 <= k < n as int - 1 implies #[trigger] arr@[k] <= arr@[k + 1] by {
                        if k == right as int - 1 {
                        }
                    };
                };
            }
            right = right - 1;
        }
        proof {
            if right == 0 {
                assert(Self::is_non_decreasing_range(arr@, 0, n as int));
                assert(arr@[left as int] <= arr@[left as int + 1]);
                assert(false);
            }
            assert(arr@[right as int - 1] > arr@[right as int]);
        }
        let mut best: usize = if n - left - 1 < right {
            n - left - 1
        } else {
            right
        };
        let ghost mut best_l: int = if n - left - 1 < right {
            left as int + 1
        } else {
            0
        };
        let ghost mut best_r: int = if n - left - 1 < right {
            n as int
        } else {
            right as int
        };
        proof {
            if n - left - 1 < right {
                assert(Self::removal_works(arr@, left as int + 1, n as int)) by {
                    assert(Self::is_non_decreasing_range(arr@, 0, left as int + 1));
                    assert(Self::is_non_decreasing_range(arr@, n as int, n as int));
                };
            } else {
                assert(Self::removal_works(arr@, 0, right as int)) by {
                    assert(Self::is_non_decreasing_range(arr@, 0, 0));
                    assert(Self::is_non_decreasing_range(arr@, right as int, n as int));
                };
            }
            assert(Self::removal_works(arr@, best_l, best_r));
            assert(best == (best_r - best_l) as usize);
        }
        let mut i: usize = 0;
        let mut j: usize = right;
        while i <= left && j < n
            invariant
                n == arr.len(),
                1 <= n <= 100_000,
                0 <= left < n,
                0 < right < n,
                forall|x: int| 0 <= x < n ==> 0 <= #[trigger] arr[x] <= 1_000_000_000,
                Self::is_non_decreasing_range(arr@, 0, left as int + 1),
                Self::is_non_decreasing_range(arr@, right as int, n as int),
                arr@[left as int] > arr@[left as int + 1],
                arr@[right as int - 1] > arr@[right as int],
                0 <= i <= left + 1,
                right <= j <= n,
                0 <= best <= n,
                Self::removal_works(arr@, best_l, best_r),
                best == (best_r - best_l) as usize,
                best <= right,
                best <= n - left - 1,
                forall|p: int| 0 <= p < i as int ==> #[trigger] Self::processed_ok(arr@, right as int, p, best as int),
                i <= left ==> Self::no_bridge_before(arr@, i as int, right as int, j as int),
            decreases (n - j) + (left + 1 - i),
        {
            if arr[i] <= arr[j] {
                let ghost old_i: int = i as int;
                let ghost old_best: int = best as int;
                let candidate = j - i - 1;
                if candidate < best {
                    proof {
                        assert(Self::is_non_decreasing_range(arr@, j as int, n as int)) by {
                            assert forall|k: int| j as int <= k < n as int - 1 implies #[trigger] arr@[k] <= arr@[k + 1] by {
                                assert(right as int <= k);
                            };
                        };
                        assert(Self::removal_works(arr@, i as int + 1, j as int)) by {
                            assert(Self::is_non_decreasing_range(arr@, 0, i as int + 1));
                            assert(Self::is_non_decreasing_range(arr@, j as int, n as int));
                        };
                        best_l = i as int + 1;
                        best_r = j as int;
                    }
                    best = candidate;
                }
                proof {
                    assert(best as int <= old_best);
                    assert(best as int <= j as int - old_i - 1);
                    assert(Self::removal_works(arr@, best_l, best_r));
                    assert(best == (best_r - best_l) as usize);
                    assert forall|p: int| 0 <= p < old_i + 1 implies #[trigger] Self::processed_ok(arr@, right as int, p, best as int) by {
                        if p < old_i {
                            assert(Self::processed_ok(arr@, right as int, p, old_best));
                            assert(Self::processed_ok(arr@, right as int, p, best as int)) by {
                                assert forall|q: int| right as int <= q < n as int && arr@[p] <= arr@[q] implies best as int <= q - p - 1 by {
                                    assert(old_best <= q - p - 1);
                                };
                            };
                        } else {
                            assert(p == old_i);
                            assert(Self::processed_ok(arr@, right as int, p, best as int)) by {
                                assert forall|q: int| right as int <= q < n as int && arr@[p] <= arr@[q] implies best as int <= q - p - 1 by {
                                    if q < j as int {
                                        assert(arr@[q] < arr@[p]);
                                        assert(false);
                                    }
                                    assert(q >= j as int);
                                };
                            };
                        }
                    };
                    if old_i < left as int {
                        assert(Self::no_bridge_before(arr@, old_i + 1, right as int, j as int)) by {
                            assert forall|q: int| right as int <= q < j as int implies #[trigger] arr@[q] < arr@[old_i + 1] by {
                                assert(arr@[q] < arr@[old_i]);
                                assert(arr@[old_i] <= arr@[old_i + 1]);
                            };
                        };
                    }
                }
                i = i + 1;
            } else {
                proof {
                    assert(Self::no_bridge_before(arr@, i as int, right as int, j as int + 1)) by {
                        assert forall|q: int| right as int <= q < j as int + 1 implies #[trigger] arr@[q] < arr@[i as int] by {
                            if q < j as int {
                            } else {
                                assert(q == j as int);
                            }
                        };
                    };
                }
                j = j + 1;
            }
        }
        proof {
            assert(Self::removal_works(arr@, best_l, best_r));
            assert(best == (best_r - best_l) as usize);
            assert forall|l: int, r: int| Self::removal_works(arr@, l, r) implies best as int <= r - l by {
                if l == 0 {
                    if r < n as int {
                        Self::lemma_suffix_bound(arr@, right as int, r);
                        assert(right as int <= r);
                        assert(best as int <= right as int);
                    } else {
                        assert(best as int <= n as int);
                    }
                } else if r == n as int {
                    Self::lemma_prefix_bound(arr@, left as int, l);
                    assert(l <= left as int + 1);
                    assert(best as int <= n as int - left as int - 1);
                } else {
                    Self::lemma_prefix_bound(arr@, left as int, l);
                    Self::lemma_suffix_bound(arr@, right as int, r);
                    let p = l - 1;
                    if p < i as int {
                        assert(arr@[p] <= arr@[r]);
                        assert(Self::processed_ok(arr@, right as int, p, best as int));
                    } else {
                        assert(i <= left);
                        assert(j == n);
                        assert(right as int <= r < n as int);
                        assert(Self::no_bridge_before(arr@, i as int, right as int, n as int));
                        assert(arr@[r] < arr@[i as int]);
                        Self::lemma_sorted_range_order(arr@, 0, left as int + 1, i as int, p);
                        assert(arr@[i as int] <= arr@[p]);
                        assert(arr@[p] > arr@[r]);
                        assert(arr@[p] <= arr@[r]);
                        assert(false);
                    }
                }
            };
            assert(exists|l: int, r: int| Self::removal_works(arr@, l, r) && best as int == r - l) by {
                let l = best_l;
                let r = best_r;
                assert(Self::removal_works(arr@, l, r));
                assert(best as int == r - l);
            };
        }
        best as i32
    }
}

}
