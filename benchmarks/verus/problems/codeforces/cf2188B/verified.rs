use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_independent(t: Seq<i32>) -> bool {
        forall|k: int|
            0 <= k < t.len() - 1 ==> !(#[trigger] t[k] == 1 && t[k + 1] == 1)
    }

    pub open spec fn spec_maximal_independent(t: Seq<i32>) -> bool {
        Self::spec_independent(t) && (forall|k: int|
            0 <= k < t.len() ==> (#[trigger] t[k] == 1 || (k > 0 && t[k - 1] == 1)
                || (k + 1 < t.len() && t[k + 1] == 1)))
    }

    pub open spec fn spec_extends(initial: Seq<i32>, t: Seq<i32>) -> bool {
        initial.len() == t.len() && (forall|k: int|
            0 <= k < initial.len() ==> (#[trigger] initial[k] == 1 ==> t[k] == 1))
    }

    pub open spec fn spec_sum_ones_helper(s: Seq<i32>, i: int) -> int
        decreases s.len() - i,
    {
        if i >= s.len() {
            0int
        } else {
            (if s[i] == 1 {
                1int
            } else {
                0int
            }) + Self::spec_sum_ones_helper(s, i + 1)
        }
    }

    pub open spec fn spec_sum_ones(s: Seq<i32>) -> int {
        Self::spec_sum_ones_helper(s, 0)
    }

    pub open spec fn spec_run_end(s: Seq<i32>, i: int) -> int
        recommends
            0 <= i < s.len(),
            s[i] == 0,
        decreases s.len() - i,
    {
        if i + 1 < s.len() && s[i + 1] == 0 {
            Self::spec_run_end(s, i + 1)
        } else {
            i + 1
        }
    }

    pub open spec fn spec_run_extra(l: int, left: bool, right: bool) -> int {
        if left && right {
            l / 3
        } else if left || right {
            (l + 1) / 3
        } else {
            (l + 2) / 3
        }
    }

    proof fn lemma_spec_run_extra_le_l(l: int, left: bool, right: bool)
        requires
            l >= 1,
        ensures
            Self::spec_run_extra(l, left, right) <= l,
    {
        if left && right {
            assert(l == 3 * (l / 3) + l % 3);
            assert(l / 3 <= l);
        } else if left || right {
            assert(l + 1 == 3 * ((l + 1) / 3) + (l + 1) % 3);
            assert((l + 1) / 3 <= l + 1);
            assert((l + 1) / 3 <= l);
        } else {
            assert(l + 2 == 3 * ((l + 2) / 3) + (l + 2) % 3);
            assert((l + 2) / 3 <= (l + 2));
            assert(l + 2 <= 3 * l) by {
                assert(2 <= 2 * l);
            };
            assert((l + 2) / 3 <= l);
        }
    }

    proof fn lemma_spec_run_end_segment_all_zeros(s: Seq<i32>, i: int)
        requires
            0 <= i < s.len(),
            s[i] == 0,
        ensures
            forall|k: int|
                i <= k < Self::spec_run_end(s, i) ==> #[trigger] s[k] == 0,
        decreases s.len() - i,
    {
        let j = Self::spec_run_end(s, i);
        Self::lemma_run_end_bounds(s, i);
        assert(i + 1 <= j && j <= s.len());
        if i + 1 >= s.len() {
            assert(j == i + 1);
            assert(forall|k: int| i <= k < j ==> s[k] == 0);
        } else if s[i + 1] != 0 {
            assert(j == i + 1);
            assert(forall|k: int| i <= k < j ==> s[k] == 0);
        } else {
            assert(s[i + 1] == 0);
            assert(j == Self::spec_run_end(s, i + 1));
            assert(0 <= i + 1 && i + 1 < s.len());
            Self::lemma_spec_run_end_segment_all_zeros(s, i + 1);
            assert(forall|k: int| i + 1 <= k < j ==> s[k] == 0);
            assert(forall|k: int| i <= k < j ==> s[k] == 0);
        }
    }

    pub broadcast proof fn lemma_run_end_bounds(s: Seq<i32>, i: int)
        requires
            0 <= i < s.len(),
            #[trigger] s[i] == 0,
        ensures
            i + 1 <= Self::spec_run_end(s, i) && Self::spec_run_end(s, i) <= s.len(),
        decreases s.len() - i,
    {
        if i + 1 >= s.len() {
            assert(Self::spec_run_end(s, i) == i + 1);
            assert(Self::spec_run_end(s, i) == s.len());
            assert(i + 1 <= Self::spec_run_end(s, i) && Self::spec_run_end(s, i) <= s.len());
        } else if s[i + 1] != 0 {
            assert(Self::spec_run_end(s, i) == i + 1);
            assert(i + 1 <= Self::spec_run_end(s, i) && Self::spec_run_end(s, i) <= s.len());
        } else {
            assert(s[i + 1] == 0);
            assert(Self::spec_run_end(s, i) == Self::spec_run_end(s, i + 1));
            Self::lemma_run_end_bounds(s, i + 1);
            assert(
                i + 1 <= Self::spec_run_end(s, i + 1) && Self::spec_run_end(s, i + 1) <= s.len()
            );
            assert(i + 1 <= Self::spec_run_end(s, i) && Self::spec_run_end(s, i) <= s.len());
        }
    }

    pub broadcast proof fn lemma_run_end_gt(s: Seq<i32>, i: int)
        requires
            0 <= i < s.len(),
            #[trigger] s[i] == 0,
        ensures
            Self::spec_run_end(s, i) > i,
        decreases s.len() - i,
    {
        if i + 1 >= s.len() {
            assert(Self::spec_run_end(s, i) == i + 1);
            assert(i + 1 == s.len());
            assert(i + 1 > i);
        } else if s[i + 1] != 0 {
            assert(Self::spec_run_end(s, i) == i + 1);
            assert(i + 1 > i);
        } else {
            assert(s[i + 1] == 0);
            assert(Self::spec_run_end(s, i) == Self::spec_run_end(s, i + 1));
            Self::lemma_run_end_gt(s, i + 1);
            assert(Self::spec_run_end(s, i + 1) > i + 1);
            assert(Self::spec_run_end(s, i) > i);
        }
    }

    pub open spec fn spec_addon_from_index(s: Seq<i32>, i: int) -> int
        recommends
            0 <= i <= s.len(),
            forall|k: int| 0 <= k < s.len() as int ==> #[trigger] s[k] == 0 || s[k] == 1,
        decreases s.len() - i,
    {
        if i < 0 {
            0int
        } else if i >= s.len() {
            0int
        } else {
            if s[i] == 1 {
                Self::spec_addon_from_index(s, i + 1)
            } else if s[i] == 0 {
                let j = Self::spec_run_end(s, i);
                let l = j - i;
                let left = i > 0 && s[i - 1] == 1;
                proof {
                    assert(0 <= i);
                    assert(i < s.len());
                    assert(s[i] == 0);
                    if i + 1 < s.len() && s[i + 1] == 0 {
                        assert(0 <= i + 1 && i + 1 < s.len());
                        assert(s[i + 1] == 0);
                        assert(Self::spec_run_end(s, i) == Self::spec_run_end(s, i + 1));
                        Self::lemma_run_end_gt(s, i + 1);
                        Self::lemma_run_end_bounds(s, i + 1);
                    } else {
                        assert(Self::spec_run_end(s, i) == i + 1);
                        assert(i + 1 > i);
                        assert(i + 1 <= s.len());
                    }
                    assert(j > i);
                    assert(j <= s.len());
                    assert(s.len() - j < s.len() - i);
                }
                let right = if j < s.len() {
                    s[j] == 1
                } else {
                    false
                };
                Self::spec_run_extra(l, left, right) + Self::spec_addon_from_index(s, j)
            } else {
                0int
            }
        }
    }

    pub open spec fn spec_closed_form_total(s: Seq<i32>) -> int {
        Self::spec_sum_ones(s) + Self::spec_addon_from_index(s, 0)
    }

    proof fn lemma_sum_ones_helper_tail(s: Seq<i32>, i: int)
        requires
            0 <= i < s.len(),
        ensures
            Self::spec_sum_ones_helper(s, i) == (if s[i] == 1 {
                1int
            } else {
                0int
            }) + Self::spec_sum_ones_helper(s, i + 1),
    {
    }

    proof fn lemma_addon_at_one(s: Seq<i32>, i: int)
        requires
            0 <= i < s.len(),
            s[i] == 1,
            forall|k: int| 0 <= k < s.len() as int ==> #[trigger] s[k] == 0 || s[k] == 1,
        ensures
            Self::spec_addon_from_index(s, i) == Self::spec_addon_from_index(s, i + 1),
    {
        assert(0 <= i && i < s.len());
        assert(s[i] == 1);
        assert(Self::spec_addon_from_index(s, i) == Self::spec_addon_from_index(s, i + 1));
    }

    proof fn lemma_addon_at_zero(s: Seq<i32>, i: int)
        requires
            0 <= i < s.len(),
            s[i] == 0,
            forall|k: int| 0 <= k < s.len() as int ==> #[trigger] s[k] == 0 || s[k] == 1,
        ensures
            Self::spec_addon_from_index(s, i) == Self::spec_run_extra(
                Self::spec_run_end(s, i) - i,
                i > 0 && s[i - 1] == 1,
                Self::spec_run_end(s, i) < s.len() && s[Self::spec_run_end(s, i)] == 1,
            ) + Self::spec_addon_from_index(s, Self::spec_run_end(s, i)),
    {
        let j = Self::spec_run_end(s, i);
        Self::lemma_run_end_gt(s, i);
        Self::lemma_run_end_bounds(s, i);
        assert(j > i);
        assert(0 <= j && j <= s.len());
        if j < s.len() {
            assert(0 <= j && j < s.len());
        }
        assert(s.len() - j < s.len() - i);
        assert(Self::spec_addon_from_index(s, i) == Self::spec_run_extra(
            j - i,
            i > 0 && s[i - 1] == 1,
            if j < s.len() {
                s[j] == 1
            } else {
                false
            },
        ) + Self::spec_addon_from_index(s, j));
    }

    proof fn lemma_spec_addon_from_index_nonneg(s: Seq<i32>, i: int)
        requires
            0 <= i <= s.len(),
            forall|k: int| 0 <= k < s.len() as int ==> #[trigger] s[k] == 0 || s[k] == 1,
        ensures
            Self::spec_addon_from_index(s, i) >= 0int,
        decreases s.len() - i,
    {
        if i < 0 {
        } else if i >= s.len() {
        } else if s[i] == 1 {
            Self::lemma_spec_addon_from_index_nonneg(s, i + 1);
        } else if s[i] == 0 {
            let j = Self::spec_run_end(s, i);
            Self::lemma_run_end_gt(s, i);
            Self::lemma_run_end_bounds(s, i);
            assert(j > i);
            assert(j <= s.len());
            assert(0 <= Self::spec_run_extra(j - i, i > 0 && s[i - 1] == 1, j < s.len() && s[j] == 1));
            Self::lemma_spec_addon_from_index_nonneg(s, j);
            assert(Self::spec_addon_from_index(s, i) >= 0int);
        } else {
        }
    }

    proof fn lemma_spec_sum_ones_helper_nonneg(s: Seq<i32>, i: int)
        requires
            0 <= i <= s.len(),
        ensures
            Self::spec_sum_ones_helper(s, i) >= 0int,
        decreases s.len() - i,
    {
        if i >= s.len() {
        } else {
            Self::lemma_spec_sum_ones_helper_nonneg(s, i + 1);
        }
    }

    proof fn lemma_sum_ones_prefix_zero_run(s: Seq<i32>, i: int, j: int)
        requires
            0 <= i < j <= s.len(),
            forall|k: int| i <= k < j ==> #[trigger] s[k] == 0,
        ensures
            Self::spec_sum_ones_helper(s, i) == Self::spec_sum_ones_helper(s, j),
        decreases j - i,
    {
        if i + 1 < j {
            assert(s[i] == 0);
            Self::lemma_sum_ones_helper_tail(s, i);
            assert(Self::spec_sum_ones_helper(s, i) == Self::spec_sum_ones_helper(s, i + 1));
            Self::lemma_sum_ones_prefix_zero_run(s, i + 1, j);
        } else {
            assert(i + 1 == j);
            assert(s[i] == 0);
            Self::lemma_sum_ones_helper_tail(s, i);
            assert(Self::spec_sum_ones_helper(s, i) == Self::spec_sum_ones_helper(s, j));
        }
    }

    proof fn lemma_spec_sum_ones_helper_plus_addon_le_suffix(s: Seq<i32>, i: int)
        requires
            forall|k: int| 0 <= k < s.len() as int ==> #[trigger] s[k] == 0 || s[k] == 1,
            0 <= i <= s.len(),
        ensures
            Self::spec_sum_ones_helper(s, i) + Self::spec_addon_from_index(s, i) <= s.len() - i,
        decreases s.len() - i,
    {
        if i >= s.len() {
            assert(Self::spec_sum_ones_helper(s, i) == 0int);
            assert(Self::spec_addon_from_index(s, i) == 0int);
            assert(s.len() - i == 0);
        } else if s[i] == 1 {
            let ip1 = i + 1;
            Self::lemma_spec_sum_ones_helper_plus_addon_le_suffix(s, ip1);
            Self::lemma_sum_ones_helper_tail(s, i);
            Self::lemma_addon_at_one(s, i);
            assert(
                Self::spec_sum_ones_helper(s, i) + Self::spec_addon_from_index(s, i) == 1int
                    + Self::spec_sum_ones_helper(s, ip1) + Self::spec_addon_from_index(s, ip1)
            );
            assert(
                Self::spec_sum_ones_helper(s, ip1) + Self::spec_addon_from_index(s, ip1)
                    <= s.len() - ip1
            );
            assert(
                1int + Self::spec_sum_ones_helper(s, ip1) + Self::spec_addon_from_index(s, ip1)
                    <= s.len() - i
            );
        } else if s[i] == 0 {
            let j = Self::spec_run_end(s, i);
            Self::lemma_run_end_gt(s, i);
            Self::lemma_run_end_bounds(s, i);
            assert(i < j && j <= s.len());
            let l = j - i;
            assert(l >= 1);
            Self::lemma_spec_run_end_segment_all_zeros(s, i);
            Self::lemma_sum_ones_prefix_zero_run(s, i, j);
            Self::lemma_addon_at_zero(s, i);
            Self::lemma_spec_run_extra_le_l(l, i > 0 && s[i - 1] == 1, j < s.len() && s[j] == 1);
            Self::lemma_spec_sum_ones_helper_plus_addon_le_suffix(s, j);
            assert(Self::spec_sum_ones_helper(s, i) == Self::spec_sum_ones_helper(s, j));
            assert(
                Self::spec_addon_from_index(s, i) == Self::spec_run_extra(
                    l,
                    i > 0 && s[i - 1] == 1,
                    j < s.len() && s[j] == 1,
                ) + Self::spec_addon_from_index(s, j)
            );
            assert(
                Self::spec_sum_ones_helper(s, j) + Self::spec_addon_from_index(s, j) <= s.len()
                    - j
            );
            assert(
                Self::spec_run_extra(l, i > 0 && s[i - 1] == 1, j < s.len() && s[j] == 1) <= l
            );
            assert(
                Self::spec_sum_ones_helper(s, i) + Self::spec_addon_from_index(s, i) <= s.len()
                    - j + l
            );
            assert(s.len() - j + l == s.len() - i);
        } else {
            assert(false);
        }
    }

    proof fn lemma_spec_closed_form_total_le_len(s: Seq<i32>)
        requires
            forall|k: int| 0 <= k < s.len() as int ==> #[trigger] s[k] == 0 || s[k] == 1,
        ensures
            Self::spec_closed_form_total(s) <= s.len(),
    {
        Self::lemma_spec_sum_ones_helper_plus_addon_le_suffix(s, 0);
        assert(Self::spec_sum_ones(s) == Self::spec_sum_ones_helper(s, 0));
        assert(
            Self::spec_closed_form_total(s) == Self::spec_sum_ones_helper(s, 0)
                + Self::spec_addon_from_index(s, 0)
        );
    }

    proof fn lemma_exec_extra_eq_spec_run_extra(l: usize, left: bool, right: bool)
        requires
            l >= 1,
            l <= 200_000,
        ensures
            (if left && right {
                (l as i64) / 3
            } else if left || right {
                ((l as i64) + 1) / 3
            } else {
                ((l as i64) + 2) / 3
            }) as int == Self::spec_run_extra(l as int, left, right),
    {
        let li = l as int;
        assert(li >= 1);
        assert(l as i64 == li);
        if left && right {
            assert((l as i64) / 3 == li / 3);
        } else if left || right {
            assert(((l as i64) + 1) / 3 == (li + 1) / 3);
        } else {
            assert(((l as i64) + 2) / 3 == (li + 2) / 3);
        }
    }

    fn zero_run_end(s: &Vec<i32>, i: usize) -> (j_end: usize)
        requires
            i < s.len(),
            s@[i as int] == 0,
            forall|k: int|
                0 <= k < s.len() as int ==> #[trigger] s[k] == 0 || s[k] == 1,
        ensures
            j_end as int == Self::spec_run_end(s@, i as int),
            i < j_end <= s.len(),
            forall|k: int|
                i <= k < j_end as int ==> #[trigger] s@[k] == 0,
            j_end as int == s.len() as int || s@[j_end as int] == 1,
        decreases s.len() - i,
    {
        let n = s.len();
        if i + 1 >= n {
            let j_end = i + 1;
            proof {
                assert(Self::spec_run_end(s@, i as int) == j_end as int);
                assert(forall|k: int|
                    i as int <= k < j_end as int ==> #[trigger] s@[k] == 0);
                assert(j_end as int == s.len() as int || s@[j_end as int] == 1);
            }
            j_end
        } else {
            proof {
                assert(i + 1 < n);
            }
            if s[i + 1] != 0 {
                let j_end = i + 1;
                proof {
                    assert(Self::spec_run_end(s@, i as int) == j_end as int);
                    assert(s@[j_end as int] == 1);
                    assert(forall|k: int|
                        i as int <= k < j_end as int ==> #[trigger] s@[k] == 0);
                }
                j_end
            } else {
                proof {
                    assert(s@[(i + 1) as int] == 0);
                    assert(Self::spec_run_end(s@, i as int) == Self::spec_run_end(s@, (i + 1) as int));
                    assert(n - (i + 1) < n - i);
                }
                Self::zero_run_end(s, i + 1)
            }
        }
    }

    pub fn min_total_seated_students(s: &Vec<i32>) -> (res: i64)
        requires
            1 <= s.len() <= 200_000,
            forall|k: int|
                0 <= k < s.len() as int ==> #[trigger] s[k] == 0 || s[k] == 1,
            forall|k: int|
                0 <= k < s.len() as int - 1 ==> !(#[trigger] s[k] == 1 && s[k + 1] == 1),
        ensures
            res as int == Self::spec_closed_form_total(s@),
    {
        proof {
            Self::lemma_spec_closed_form_total_le_len(s@);
            Self::lemma_spec_addon_from_index_nonneg(s@, 0);
            Self::lemma_spec_sum_ones_helper_nonneg(s@, 0);
        }
        let n = s.len();
        proof {
            assert(n <= 200_000);
        }
        let mut ones: i64 = 0;
        let mut add: i64 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                n == s.len(),
                n <= 200_000,
                0 <= i <= n,
                forall|k: int|
                    0 <= k < s.len() as int ==> #[trigger] s@[k] == 0 || s@[k] == 1,
                forall|k: int|
                    0 <= k < s.len() as int - 1 ==> !(#[trigger] s@[k] == 1 && s@[k + 1] == 1),
                ones as int + add as int + Self::spec_sum_ones_helper(s@, i as int)
                    + Self::spec_addon_from_index(s@, i as int)
                    == Self::spec_closed_form_total(s@),
                Self::spec_sum_ones_helper(s@, i as int) >= 0,
                Self::spec_addon_from_index(s@, i as int) >= 0,
                Self::spec_closed_form_total(s@) <= s@.len() as int,
                ones as int >= 0,
                add as int >= 0,
            decreases n - i,
        {
            if s[i] == 1 {
                proof {
                    Self::lemma_sum_ones_helper_tail(s@, i as int);
                    Self::lemma_addon_at_one(s@, i as int);
                    let ip1 = i as int + 1;
                    assert(
                        (ones as int + 1) + add as int
                            + Self::spec_sum_ones_helper(s@, ip1) + Self::spec_addon_from_index(s@, ip1)
                            == Self::spec_closed_form_total(s@)
                    );
                    assert(
                        ones as int + add as int + Self::spec_sum_ones_helper(s@, i as int)
                            + Self::spec_addon_from_index(s@, i as int)
                            == Self::spec_closed_form_total(s@)
                    );
                    assert(Self::spec_sum_ones_helper(s@, i as int) >= 0);
                    assert(Self::spec_addon_from_index(s@, i as int) >= 0);
                    assert(ones as int + add as int <= Self::spec_closed_form_total(s@));
                    assert(ones as int <= Self::spec_closed_form_total(s@));
                    assert(ones + 1 <= 200_001);
                }
                ones = ones + 1;
                i = i + 1;
                proof {
                    Self::lemma_spec_sum_ones_helper_nonneg(s@, i as int);
                    Self::lemma_spec_addon_from_index_nonneg(s@, i as int);
                }
            } else {
                proof {
                    assert(s@[i as int] == 0);
                }
                let j_end = Self::zero_run_end(s, i);
                let l: usize = j_end - i;
                let left: bool = if i > 0 {
                    s[i - 1] == 1
                } else {
                    false
                };
                let right: bool = if j_end < n {
                    s[j_end] == 1
                } else {
                    false
                };
                let extra: i64 = if left && right {
                    (l as i64) / 3
                } else if left || right {
                    ((l as i64) + 1) / 3
                } else {
                    ((l as i64) + 2) / 3
                };
                proof {
                    Self::lemma_spec_run_end_segment_all_zeros(s@, i as int);
                    Self::lemma_sum_ones_prefix_zero_run(s@, i as int, j_end as int);
                    Self::lemma_addon_at_zero(s@, i as int);
                    assert(j_end as int == Self::spec_run_end(s@, i as int));
                    assert(j_end <= n);
                    assert(l <= j_end);
                    assert(l <= n);
                    assert(l <= 200_000);
                    Self::lemma_exec_extra_eq_spec_run_extra(l, left, right);
                    assert(extra as int == Self::spec_run_extra(l as int, left, right));
                    let j = Self::spec_run_end(s@, i as int);
                    assert(j == j_end as int);
                    assert(l as int == j - (i as int));
                    assert(
                        ones as int + add as int + Self::spec_sum_ones_helper(s@, j_end as int)
                            + Self::spec_addon_from_index(s@, j_end as int)
                            + Self::spec_run_extra(l as int, left, right)
                            == Self::spec_closed_form_total(s@)
                    );
                    assert(
                        (add as int) + (extra as int) == add as int + Self::spec_run_extra(l as int, left, right)
                    );
                    assert(
                        (add as int) + (extra as int) + ones as int
                            + Self::spec_sum_ones_helper(s@, j_end as int)
                            + Self::spec_addon_from_index(s@, j_end as int)
                            == Self::spec_closed_form_total(s@)
                    );
                    assert(
                        Self::spec_closed_form_total(s@) - ((add as int) + (extra as int)) == ones as int
                            + Self::spec_sum_ones_helper(s@, j_end as int)
                            + Self::spec_addon_from_index(s@, j_end as int)
                    );
                    assert(ones as int >= 0);
                    Self::lemma_spec_sum_ones_helper_nonneg(s@, j_end as int);
                    Self::lemma_spec_addon_from_index_nonneg(s@, j_end as int);
                    assert(Self::spec_sum_ones_helper(s@, j_end as int) >= 0);
                    assert(Self::spec_addon_from_index(s@, j_end as int) >= 0);
                    assert(
                        (add as int) + (extra as int) <= Self::spec_closed_form_total(s@)
                    );
                    assert(add + extra <= 200_000);
                }
                add = add + extra;
                i = j_end;
                proof {
                    Self::lemma_spec_sum_ones_helper_nonneg(s@, i as int);
                    Self::lemma_spec_addon_from_index_nonneg(s@, i as int);
                }
            }
        }
        proof {
            assert(i == n);
            assert(Self::spec_sum_ones_helper(s@, n as int) == 0int);
            assert(Self::spec_addon_from_index(s@, n as int) == 0int);
            assert(ones as int + add as int == Self::spec_closed_form_total(s@));
            assert(ones + add <= 200_000);
        }
        ones + add
    }
}

}
