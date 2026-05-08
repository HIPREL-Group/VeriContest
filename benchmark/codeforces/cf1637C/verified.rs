use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn ceil_half_i64(x: i64) -> int {
        ((x + 1) / 2) as int
    }

    pub open spec fn prefix_sum_ceil_half(a: Seq<i64>, end: int) -> int
        recommends
            1 <= end <= a.len(),
        decreases
            end,
    {
        if end <= 1 {
            0
        } else {
            Self::prefix_sum_ceil_half(a, end - 1) + Self::ceil_half_i64(a[end - 1])
        }
    }

    pub open spec fn sum_middle_ops(a: Seq<i64>) -> int
        recommends
            a.len() >= 3,
    {
        Self::prefix_sum_ceil_half(a, a.len() - 1)
    }

    pub open spec fn stones_impossible(a: Seq<i64>) -> bool {
        let n = a.len();
        if n == 3 {
            (a[1] as int) % 2 == 1
        } else {
            forall|i: int|
                #![trigger a[i]]
                1 <= i <= n - 2 ==> a[i] == 1
        }
    }

    pub open spec fn minimum_stone_ops_answer(a: Seq<i64>) -> int
        recommends
            a.len() >= 3,
            !Self::stones_impossible(a),
    {
        let n = a.len();
        if n == 3 {
            a[1] as int / 2
        } else {
            Self::sum_middle_ops(a)
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn minimum_stone_operations(a: Vec<i64>) -> (r: Option<i64>)
        requires
            3 <= a.len() <= 100_000,
            forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] && a[i] <= 1_000_000_000,
        ensures
            r == None::<i64> <==> Self::stones_impossible(a@),
            r != None::<i64> ==> (r->Some_0 as int) == Self::minimum_stone_ops_answer(a@),
    {
        let n = a.len();
        if n == 3 {
            let m = a[1];
            if m % 2 == 1 {
                proof { assert(Self::stones_impossible(a@)); }
                return None;
            }
            proof {
                assert(!Self::stones_impossible(a@));
                assert((m / 2) as int == Self::minimum_stone_ops_answer(a@));
            }
            return Some(m / 2);
        }
        let ghost a_spec = a@;
        proof {
            assert(a_spec == a@);
        }
        let mut all_one = true;
        let mut i: usize = 1;
        while i < n - 1
            invariant
                3 <= n <= 100_000,
                n == a.len(),
                a@ == a_spec,
                1 <= i <= n - 1,
                forall|k: int| 0 <= k < a_spec.len() ==> 1 <= #[trigger] a_spec[k] && a_spec[k] <= 1_000_000_000,
                all_one ==> forall|k: int| 1 <= k < i as int ==> #[trigger] a_spec[k] == 1,
                !all_one ==> exists|k: int| 1 <= k < i as int && #[trigger] a_spec[k] != 1,
            decreases n - 1 - i,
        {
            if a[i] != 1 {
                all_one = false;
                proof {
                    let ii = i as int;
                    assert(1 <= ii);
                    assert(ii < ii + 1);
                    assert(a_spec[i as int] != 1);
                    assert(exists|k: int| 1 <= k < (i + 1) as int && #[trigger] a_spec[k] != 1);
                }
            } else {
                proof {
                    if all_one {
                        assert(forall|k: int| 1 <= k < i as int ==> a_spec[k] == 1);
                        assert(a_spec[i as int] == 1);
                        assert forall|k: int| 1 <= k < (i + 1) as int implies a_spec[k] == 1 by {
                            if k < i as int {
                                assert(a_spec[k] == 1);
                            } else {
                                assert(k == i as int);
                            }
                        };
                    }
                }
            }
            i = i + 1;
        }
        if all_one {
            proof {
                assert(i == n - 1);
                assert(forall|k: int| 1 <= k < i as int ==> a_spec[k] == 1);
                assert forall|k: int| 1 <= k <= a_spec.len() - 2 implies #[trigger] a_spec[k] == 1 by {
                    assert(1 <= k <= a_spec.len() - 2);
                    assert(k < i as int);
                };
                assert(Self::stones_impossible(a_spec));
            }
            return None;
        }
        proof {
            assert(!all_one);
            assert(exists|k: int| 1 <= k < i as int && #[trigger] a_spec[k] != 1);
            assert(exists|k: int| 1 <= k <= a_spec.len() - 2 && #[trigger] a_spec[k] != 1) by {
                assert(i == n - 1);
                let k: int = choose|k: int| 1 <= k < i as int && a_spec[k] != 1;
                assert(1 <= k < i as int && a_spec[k] != 1);
                assert(1 <= k <= a_spec.len() - 2 && a_spec[k] != 1);
            };
            assert(!Self::stones_impossible(a_spec));
        }
        let mut s: i64 = 0;
        let mut j: usize = 1;
        while j < n - 1
            invariant
                3 <= n <= 100_000,
                n == a.len(),
                a@ == a_spec,
                1 <= j <= n - 1,
                forall|k: int| 0 <= k < a_spec.len() ==> 1 <= #[trigger] a_spec[k] && a_spec[k] <= 1_000_000_000,
                !Self::stones_impossible(a_spec),
                (s as int) == Self::prefix_sum_ceil_half(a_spec, j as int),
                0 <= s as int <= ((j as int) - 1) * 500_000_000,
            decreases n - 1 - j,
        {
            let j0 = j;
            let old_s = s;
            proof {
                assert(1 <= j0 as int <= (n as int) - 2);
                assert(0 <= (j0 as int) && (j0 as int) < a_spec.len());
                assert(a@[j0 as int] == a_spec[j0 as int]);
                assert(a_spec[j0 as int] <= 1_000_000_000);
                assert(1 <= a_spec[j0 as int]);
                assert(0 < (a_spec[j0 as int] + 1) / 2 <= 500_000_000);
                assert((old_s as int) + ((a_spec[j0 as int] + 1) / 2) as int <= (j0 as int) * 500_000_000);
                assert((j0 as int) * 500_000_000 < 9223372036854775807);
            }
            s = s + (a[j] + 1) / 2;
            j = j + 1;
            proof {
                assert(j == j0 + 1);
                assert((s as int) == (old_s as int) + ((a_spec[j0 as int] + 1) / 2) as int);
                assert(Self::prefix_sum_ceil_half(a_spec, (j0 + 1) as int)
                    == Self::prefix_sum_ceil_half(a_spec, j0 as int) + Self::ceil_half_i64(a_spec[j0 as int]));
                assert(Self::ceil_half_i64(a_spec[j0 as int]) == ((a_spec[j0 as int] + 1) / 2) as int);
                assert((s as int) == Self::prefix_sum_ceil_half(a_spec, j as int));
                assert((s as int) <= ((j as int) - 1) * 500_000_000);
            }
        }
        proof {
            assert(j == n - 1);
            assert((s as int) == Self::prefix_sum_ceil_half(a_spec, (n - 1) as int));
            assert(Self::sum_middle_ops(a_spec) == Self::prefix_sum_ceil_half(a_spec, a_spec.len() - 1));
            assert((n - 1) as int == a_spec.len() - 1);
            assert((s as int) == Self::sum_middle_ops(a_spec));
            assert((s as int) == Self::minimum_stone_ops_answer(a_spec));
        }
        Some(s)
    }
}

}
