use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub proof fn i32_cast_nonneg(x: int)
    requires
        0 <= x <= 50_000,
    ensures
        0 <= (x as i32),
        ((x as i32) as int) == x,
{
    assert(x < 0x8000_0000) by (nonlinear_arith)
        requires
            x <= 50_000,
    {}
}

pub open spec fn is_suffix_max_at(nums: Seq<i32>, rm: Seq<i32>, j: int) -> bool {
    0 <= j < nums.len()
    && rm[j] >= nums[j]
    && (forall |k: int| j <= k < nums.len() ==> nums[k] <= rm[j])
    && (exists |k: int| j <= k < nums.len() && nums[k] == rm[j])
}

impl Solution {
    pub fn max_width_ramp(nums: Vec<i32>) -> (result: i32)
        requires
            2 <= nums.len() <= 50_000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 50_000,
        ensures
            0 <= result <= nums.len() as int - 1,
            forall |i: int, j: int|
                0 <= i < j < nums.len() && nums[i] <= nums[j] ==> j - i <= result,
            result == 0 <==> (forall |i: int, j: int|
                0 <= i < j < nums.len() ==> nums[i] > nums[j]),
            result > 0 ==> (exists |i: int, j: int|
                0 <= i < j < nums.len() && nums[i] <= nums[j] && result == j - i),
    {
        let n = nums.len();
        let ghost n_int: int = n as int;

        let mut right_max: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                right_max.len() == k,
                n == nums.len(),
            decreases n - k,
        {
            right_max.push(0i32);
            k += 1;
        }

        right_max[n - 1] = nums[n - 1];

        proof {
            assert(is_suffix_max_at(nums@, right_max@, n_int - 1)) by {
                assert forall |k: int| n_int - 1 <= k < n_int implies nums@[k] <= right_max@[n_int - 1] by {
                    assert(k == n_int - 1);
                }
            }
        }

        if n >= 2 {
            let mut k: usize = n - 1;
            while k > 0
                invariant
                    0 <= k <= n - 1,
                    n == nums.len(),
                    n >= 2,
                    right_max.len() == n,
                    n_int == n as int,
                    forall |i: int| 0 <= i < n_int ==> 0 <= #[trigger] nums[i] <= 50_000,
                    forall |j: int| k as int <= j < n_int ==>
                        is_suffix_max_at(nums@, right_max@, j),
                    forall |a: int, b: int|
                        k as int <= a <= b < n_int ==> right_max@[a] >= right_max@[b],
                decreases k,
            {
                k -= 1;
                let ghost old_rm = right_max@;
                if nums[k] > right_max[k + 1] {
                    right_max[k] = nums[k];
                } else {
                    right_max[k] = right_max[k + 1];
                }

                proof {
                    assert(is_suffix_max_at(nums@, right_max@, k as int)) by {
                        assert(is_suffix_max_at(nums@, old_rm, (k + 1) as int));
                        let rm_k = right_max@[k as int];
                        if nums@[k as int] > old_rm[(k + 1) as int] {
                            assert(rm_k == nums@[k as int]);
                            assert forall |j: int| k as int <= j < n_int
                                implies nums@[j] <= rm_k by {
                                if j > k as int {
                                    assert(nums@[j] <= old_rm[(k + 1) as int]);
                                }
                            }
                        } else {
                            assert(rm_k == old_rm[(k + 1) as int]);
                            assert forall |j: int| k as int <= j < n_int
                                implies nums@[j] <= rm_k by {
                                if j > k as int {
                                    assert(nums@[j] <= old_rm[(k + 1) as int]);
                                }
                            }
                            let wit = choose |w: int|
                                (k + 1) as int <= w < n_int && nums@[w] == old_rm[(k + 1) as int];
                            assert(k as int <= wit < n_int && nums@[wit] == rm_k);
                        }
                    }
                    assert forall |j: int| k as int <= j < n_int
                        implies is_suffix_max_at(nums@, right_max@, j) by {
                        if j > k as int {
                            assert(right_max@[j] == old_rm[j]);
                            assert(is_suffix_max_at(nums@, old_rm, j));
                        }
                    }
                    assert forall |a: int, b: int| k as int <= a <= b < n_int
                        implies right_max@[a] >= right_max@[b] by {
                        if a == k as int {
                            if b == k as int {
                            } else {
                                assert(right_max@[k as int] >= right_max@[(k + 1) as int]) by {
                                    if nums@[k as int] > old_rm[(k + 1) as int] {
                                        assert(right_max@[k as int] == nums@[k as int]);
                                        assert(right_max@[(k + 1) as int] == old_rm[(k + 1) as int]);
                                    } else {
                                        assert(right_max@[k as int] == old_rm[(k + 1) as int]);
                                        assert(right_max@[(k + 1) as int] == old_rm[(k + 1) as int]);
                                    }
                                }
                                if b > (k + 1) as int {
                                    assert(old_rm[(k + 1) as int] >= old_rm[b]);
                                    assert(right_max@[(k + 1) as int] == old_rm[(k + 1) as int]);
                                    assert(right_max@[b] == old_rm[b]);
                                }
                            }
                        } else {
                            assert(right_max@[a] == old_rm[a]);
                            assert(right_max@[b] == old_rm[b]);
                        }
                    }
                }
            }
        }

        proof {
            assert forall |j: int| 0 <= j < n_int
                implies is_suffix_max_at(nums@, right_max@, j) by {
                if n < 2 {
                    assert(j == 0);
                    assert(j == n_int - 1);
                }
            }
            assert forall |a: int, b: int| 0 <= a <= b < n_int
                implies right_max@[a] >= right_max@[b] by {
                if n < 2 {
                    assert(a == 0 && b == 0);
                }
            }
        }

        let mut best: i32 = 0;
        let ghost mut best_int: int = 0;
        let ghost mut wit_i: int = 0;
        let ghost mut wit_j: int = 0;
        let mut i: usize = 0;
        let mut j: usize = 0;

        while j < n
            invariant
                n == nums.len(),
                n_int == n as int,
                n_int <= 50_000,
                right_max.len() == n,
                forall |idx: int| 0 <= idx < n_int ==> 0 <= #[trigger] nums[idx] <= 50_000,
                forall |idx: int| 0 <= idx < n_int ==>
                    is_suffix_max_at(nums@, right_max@, idx),
                forall |a: int, b: int| 0 <= a <= b < n_int
                    ==> right_max@[a] >= right_max@[b],
                0 <= i <= j <= n,
                0 <= best_int,
                best_int <= n_int - 1 || best_int == 0,
                best == best_int as i32,
                forall |a: int, b: int|
                    #![trigger nums@[a], nums@[b]]
                    0 <= a < b < n_int && nums@[a] <= nums@[b]
                    && (a < i as int || b < j as int)
                    ==> b - a <= best_int,
                best_int > 0 ==> (
                    0 <= wit_i < wit_j < n_int
                    && nums@[wit_i] <= nums@[wit_j]
                    && wit_j - wit_i >= best_int
                ),
            decreases 2 * n - i - j,
        {
            if nums[i] <= right_max[j] {
                let width = (j - i) as i32;
                let ghost w: int = j as int - i as int;
                proof {
                    assert(0 <= w);
                    assert(w < n_int) by (nonlinear_arith)
                        requires 0 <= i as int, w + i as int == j as int, (j as int) < n_int,
                    {}
                    assert(w <= 50_000) by (nonlinear_arith)
                        requires 0 <= w, w < n_int, n_int <= 50_000,
                    {}
                    i32_cast_nonneg(w);
                }
                let ghost old_best = best_int;
                if width > best {
                    best = width;
                    proof {
                        i32_cast_nonneg(old_best);
                        assert(w > old_best);
                        best_int = w;
                        assert(is_suffix_max_at(nums@, right_max@, j as int));
                        let k = choose |k: int|
                            j as int <= k < n_int && nums@[k] == right_max@[j as int];
                        assert(nums@[i as int] <= right_max@[j as int]);
                        assert(nums@[i as int] <= nums@[k]);
                        wit_i = i as int;
                        wit_j = k;
                    }
                }
                proof {
                    assert forall |a: int, b: int|
                        #![trigger nums@[a], nums@[b]]
                        0 <= a < b < n_int && nums@[a] <= nums@[b]
                        && (a < i as int || b < j as int + 1)
                        implies b - a <= best_int by {
                        if a < i as int || b < j as int {
                        } else {
                            assert(b - a <= w) by {
                                assert(a >= i as int);
                                assert(b <= j as int);
                            }
                            if w > old_best {
                                assert(best_int == w);
                            } else {
                                i32_cast_nonneg(old_best);
                            }
                        }
                    }
                }
                j += 1;
            } else {
                proof {
                    assert forall |a: int, b: int|
                        #![trigger nums@[a], nums@[b]]
                        0 <= a < b < n_int && nums@[a] <= nums@[b]
                        && (a < i as int + 1 || b < j as int)
                        implies b - a <= best_int by {
                        if a < i as int || b < j as int {
                        } else {
                            assert(is_suffix_max_at(nums@, right_max@, b));
                            assert(nums@[b] <= right_max@[b]);
                            assert(right_max@[b] <= right_max@[j as int]) by {
                                assert(0 <= (j as int) && (j as int) <= b && b < n_int);
                            }
                            assert(nums@[b] <= right_max@[j as int]);
                            assert(!(nums@[i as int] <= right_max@[j as int]));
                            assert(0 <= nums@[i as int] <= 50_000);
                            assert(is_suffix_max_at(nums@, right_max@, j as int));
                            assert(0 <= right_max@[j as int]) by {
                                assert(right_max@[j as int] >= nums@[j as int]);
                                assert(0 <= nums@[j as int]);
                            }
                            assert(nums@[b] < nums@[i as int]) by {
                                assert(0 <= right_max@[j as int] <= 50_000) by {
                                    let w2 = choose |k2: int|
                                        j as int <= k2 < n_int && nums@[k2] == right_max@[j as int];
                                    assert(0 <= nums@[w2] <= 50_000);
                                }
                                i32_cast_nonneg(nums@[i as int] as int);
                                i32_cast_nonneg(right_max@[j as int] as int);
                            }
                            assert(nums@[a] <= nums@[b]);
                            assert(a == i as int);
                            assert(nums@[i as int] <= nums@[b]);
                            assert(false);
                        }
                    }
                }
                i += 1;
                if i > j {
                    j = i;
                }
            }
        }

        proof {
            assert forall |a: int, b: int|
                #![trigger nums@[a], nums@[b]]
                0 <= a < b < n_int && nums@[a] <= nums@[b]
                implies b - a <= best_int by {
                assert(b < j as int);
            }

            if best_int > 0 {
                assert(wit_j - wit_i >= best_int);
                assert(wit_j - wit_i <= best_int);
                assert(wit_j - wit_i == best_int);
            }

            if best_int > 0 {
                assert(best_int == wit_j - wit_i);
                assert(best_int < n_int) by (nonlinear_arith)
                    requires wit_j < n_int, wit_i >= 0, best_int == wit_j - wit_i,
                {}
                assert(best_int <= n_int - 1);
            }

            i32_cast_nonneg(best_int);

            if best_int == 0 {
                assert forall |a: int, b: int|
                    0 <= a < b < n_int
                    implies nums@[a] > nums@[b] by {
                    if nums@[a] <= nums@[b] {
                        assert(b - a <= best_int);
                        assert(false);
                    }
                }
            } else {
                assert(exists |a: int, b: int|
                    0 <= a < b < n_int && nums@[a] <= nums@[b] && best_int == b - a) by {
                    assert(best_int == wit_j - wit_i);
                }
            }
        }

        best
    }
}

}
