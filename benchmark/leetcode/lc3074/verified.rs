use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sum_prefix(s: Seq<i32>, n: int) -> int
        decreases n,
    {
        if n <= 0 {
            0
        } else if n > s.len() {
            Self::sum_prefix(s, s.len() as int)
        } else {
            Self::sum_prefix(s, n - 1) + s[n - 1] as int
        }
    }

    pub open spec fn max_index_prefix(s: Seq<i32>, n: int) -> int
        decreases n,
    {
        if n <= 1 {
            0
        } else if n > s.len() {
            Self::max_index_prefix(s, s.len() as int)
        } else {
            let j = Self::max_index_prefix(s, n - 1);
            if s[n - 1] >= s[j] {
                n - 1
            } else {
                j
            }
        }
    }

    pub open spec fn max_value(s: Seq<i32>) -> int {
        if s.len() == 0 {
            0
        } else {
            s[Self::max_index_prefix(s, s.len() as int)] as int
        }
    }

    pub open spec fn pick_max_once(s: Seq<i32>) -> Seq<i32> {
        if s.len() == 0 {
            s
        } else {
            s.update(Self::max_index_prefix(s, s.len() as int), 0)
        }
    }

    pub open spec fn after_k(s: Seq<i32>, k: int) -> Seq<i32>
        decreases k,
    {
        if k <= 0 {
            s
        } else if k > s.len() {
            Self::after_k(s, s.len() as int)
        } else {
            Self::pick_max_once(Self::after_k(s, k - 1))
        }
    }

    pub open spec fn picked_sum_k(s: Seq<i32>, k: int) -> int
        decreases k,
    {
        if k <= 0 {
            0
        } else if k > s.len() {
            Self::picked_sum_k(s, s.len() as int)
        } else {
            Self::picked_sum_k(s, k - 1) + Self::max_value(Self::after_k(s, k - 1))
        }
    }

    pub open spec fn min_boxes_from(capacity: Seq<i32>, total: int, k: int) -> int
        decreases capacity.len() - k,
    {
        if k >= capacity.len() || Self::picked_sum_k(capacity, k) >= total {
            k
        } else {
            Self::min_boxes_from(capacity, total, k + 1)
        }
    }

    pub open spec fn minimum_boxes_spec(apple: Seq<i32>, capacity: Seq<i32>) -> int {
        let total = Self::sum_prefix(apple, apple.len() as int);
        Self::min_boxes_from(capacity, total, 0)
    }

    proof fn lemma_max_index_prefix_bounds(s: Seq<i32>, n: int)
        requires
            1 <= n <= s.len(),
        ensures
            0 <= Self::max_index_prefix(s, n) < n,
        decreases n,
    {
        if n <= 1 {
        } else {
            Self::lemma_max_index_prefix_bounds(s, n - 1);
        }
    }

    proof fn lemma_min_boxes_exact_or_full(capacity: Seq<i32>, total: int, k: int, r: int)
        requires
            0 <= k <= r <= capacity.len(),
            forall |j: int| k <= j < r ==> Self::picked_sum_k(capacity, j) < total,
            r == capacity.len() || Self::picked_sum_k(capacity, r) >= total,
        ensures
            Self::min_boxes_from(capacity, total, k) == r,
        decreases r - k,
    {
        if k < r {
            assert(k < capacity.len());
            assert(Self::picked_sum_k(capacity, k) < total);
            Self::lemma_min_boxes_exact_or_full(capacity, total, k + 1, r);
        }
    }

    pub fn minimum_boxes(apple: Vec<i32>, capacity: Vec<i32>) -> (result: i32)
        requires
            1 <= apple.len() <= 50,
            1 <= capacity.len() <= 50,
            forall |i: int| 0 <= i < apple.len() ==> 1 <= #[trigger] apple[i] <= 50,
            forall |i: int| 0 <= i < capacity.len() ==> 1 <= #[trigger] capacity[i] <= 50,
            Self::sum_prefix(apple@, apple.len() as int) <= Self::sum_prefix(capacity@, capacity.len() as int),
        ensures
            result as int == Self::minimum_boxes_spec(apple@, capacity@),
    {
        let mut total: i64 = 0;
        let mut i: usize = 0;
        while i < apple.len()
            invariant
                1 <= apple.len() <= 50,
                1 <= capacity.len() <= 50,
                forall |k: int| 0 <= k < apple.len() ==> 1 <= #[trigger] apple[k] <= 50,
                forall |k: int| 0 <= k < capacity.len() ==> 1 <= #[trigger] capacity[k] <= 50,
                Self::sum_prefix(apple@, apple.len() as int) <= Self::sum_prefix(capacity@, capacity.len() as int),
                0 <= i <= apple.len(),
                total as int == Self::sum_prefix(apple@, i as int),
                0 <= total <= 50 * i as i64,
            decreases apple.len() - i,
        {
            total = total + apple[i] as i64;
            i = i + 1;
        }

        let ghost total_spec = Self::sum_prefix(apple@, apple.len() as int);
        proof {
            assert(i == apple.len());
            assert(total as int == total_spec);
        }

        let mut need = total;
        let mut cap = capacity;
        let m = cap.len();
        let mut used: usize = 0;

        while used < m && need > 0
            invariant
                1 <= apple.len() <= 50,
                1 <= m <= 50,
                m == capacity.len(),
                m == cap.len(),
                forall |k: int| 0 <= k < apple.len() ==> 1 <= #[trigger] apple[k] <= 50,
                forall |k: int| 0 <= k < capacity.len() ==> 1 <= #[trigger] capacity[k] <= 50,
                total as int == total_spec,
                total_spec <= Self::sum_prefix(capacity@, m as int),
                0 <= used <= m,
                cap@ == Self::after_k(capacity@, used as int),
                need as int == total_spec - Self::picked_sum_k(capacity@, used as int),
                -5000 <= need <= 2500,
                forall |k: int| 0 <= k < cap.len() ==> 0 <= #[trigger] cap[k] <= 50,
                forall |j: int| 0 <= j < used ==> Self::picked_sum_k(capacity@, j) < total_spec,
            decreases m - used,
        {
            proof {
                assert(Self::picked_sum_k(capacity@, used as int) < total_spec);
            }

            let ghost cap_before = cap@;
            let ghost used_before = used as int;
            let ghost picked_before = Self::picked_sum_k(capacity@, used_before);

            let mut max_idx: usize = 0;
            let mut j: usize = 1;
            while j < m
                invariant
                    1 <= m <= 50,
                    m == cap.len(),
                    cap_before.len() == m as int,
                    cap@ == cap_before,
                    1 <= j <= m,
                    0 <= max_idx < j,
                    max_idx as int == Self::max_index_prefix(cap_before, j as int),
                decreases m - j,
            {
                let ghost old_idx = max_idx as int;
                proof {
                    assert(old_idx == Self::max_index_prefix(cap_before, j as int));
                }
                if cap[j] >= cap[max_idx] {
                    max_idx = j;
                    proof {
                        assert(cap_before[j as int] == cap[j as int]);
                        assert(cap_before[old_idx] == cap[old_idx]);
                        assert(cap_before[j as int] >= cap_before[old_idx]);
                        assert(Self::max_index_prefix(cap_before, (j + 1) as int) == j as int);
                    }
                } else {
                    proof {
                        assert(cap_before[j as int] == cap[j as int]);
                        assert(cap_before[old_idx] == cap[old_idx]);
                        assert(cap_before[j as int] < cap_before[old_idx]);
                        assert(Self::max_index_prefix(cap_before, (j + 1) as int) == old_idx);
                    }
                }
                j = j + 1;
                proof {
                    assert(max_idx as int == Self::max_index_prefix(cap_before, j as int));
                }
            }

            proof {
                assert(j == m);
                assert(max_idx as int == Self::max_index_prefix(cap_before, m as int));
                Self::lemma_max_index_prefix_bounds(cap_before, m as int);
            }

            let max_cap = cap[max_idx];
            need = need - cap[max_idx] as i64;
            cap.set(max_idx, 0);
            used = used + 1;

            proof {
                assert(cap_before.len() == m as int);
                assert(max_cap as int == Self::max_value(cap_before));
                assert(cap@ == cap_before.update(max_idx as int, 0));
                assert(cap_before.update(max_idx as int, 0) == Self::pick_max_once(cap_before));
                assert(Self::after_k(capacity@, used as int) == Self::pick_max_once(Self::after_k(capacity@, used_before)));
                assert(Self::after_k(capacity@, used_before) == cap_before);
                assert(cap@ == Self::after_k(capacity@, used as int));

                assert(Self::picked_sum_k(capacity@, used as int)
                    == Self::picked_sum_k(capacity@, used_before) + Self::max_value(Self::after_k(capacity@, used_before)));
                assert(Self::max_value(Self::after_k(capacity@, used_before)) == max_cap as int);
                assert(Self::picked_sum_k(capacity@, used as int) == picked_before + max_cap as int);
                assert(need as int == total_spec - Self::picked_sum_k(capacity@, used as int));
                assert(-5000 <= need <= 2500);
                assert forall |k: int| 0 <= k < cap.len() implies 0 <= #[trigger] cap[k] <= 50 by {
                    if k == max_idx as int {
                    } else {
                        assert(cap[k] == cap_before[k]);
                    }
                };

                assert forall |x: int| 0 <= x < used implies Self::picked_sum_k(capacity@, x) < total_spec by {
                    if x < used_before {
                        assert(Self::picked_sum_k(capacity@, x) < total_spec);
                    } else {
                        assert(x == used_before);
                        assert(Self::picked_sum_k(capacity@, used_before) < total_spec);
                    }
                };
            }
        }

        proof {
            assert(used <= m);
            assert(used == m || Self::picked_sum_k(capacity@, used as int) >= total_spec);
            Self::lemma_min_boxes_exact_or_full(capacity@, total_spec, 0, used as int);
            assert(Self::minimum_boxes_spec(apple@, capacity@) == used as int);
        }

        used as i32
    }
}

}
