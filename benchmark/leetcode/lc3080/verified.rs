use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn best_in_prefix(nums: Seq<i32>, marked: Seq<bool>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            nums.len() as int
        } else {
            let prev = Self::best_in_prefix(nums, marked, end - 1);
            let j = end - 1;
            if marked[j] {
                prev
            } else if prev == nums.len() as int || nums[j] < nums[prev] || (nums[j] == nums[prev] && j < prev) {
                j
            } else {
                prev
            }
        }
    }

    pub open spec fn best_unmarked(nums: Seq<i32>, marked: Seq<bool>) -> int {
        Self::best_in_prefix(nums, marked, nums.len() as int)
    }

    pub open spec fn sum_unmarked_prefix(nums: Seq<i32>, marked: Seq<bool>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::sum_unmarked_prefix(nums, marked, end - 1)
                + if marked[end - 1] { 0 } else { nums[end - 1] as int }
        }
    }

    pub open spec fn sum_unmarked(nums: Seq<i32>, marked: Seq<bool>) -> int {
        Self::sum_unmarked_prefix(nums, marked, nums.len() as int)
    }

    pub open spec fn all_unmarked(n: int) -> Seq<bool>
        decreases n,
    {
        if n <= 0 {
            seq![]
        } else {
            Self::all_unmarked(n - 1).push(false)
        }
    }

    pub open spec fn mark_index(marked: Seq<bool>, idx: int) -> Seq<bool> {
        if marked[idx] {
            marked
        } else {
            marked.update(idx, true)
        }
    }

    pub open spec fn mark_steps(nums: Seq<i32>, marked: Seq<bool>, steps: int) -> Seq<bool>
        decreases steps,
    {
        if steps <= 0 {
            marked
        } else {
            let prev = Self::mark_steps(nums, marked, steps - 1);
            let b = Self::best_unmarked(nums, prev);
            if b == nums.len() as int {
                prev
            } else {
                prev.update(b, true)
            }
        }
    }

    pub open spec fn apply_query(nums: Seq<i32>, marked: Seq<bool>, query: Vec<i32>) -> Seq<bool> {
        let marked1 = Self::mark_index(marked, query[0] as int);
        Self::mark_steps(nums, marked1, query[1] as int)
    }

    pub open spec fn state_after(nums: Seq<i32>, queries: Seq<Vec<i32>>, t: int) -> Seq<bool>
        decreases t,
    {
        if t <= 0 {
            Self::all_unmarked(nums.len() as int)
        } else {
            let prev = Self::state_after(nums, queries, t - 1);
            Self::apply_query(nums, prev, queries[t - 1])
        }
    }

    pub open spec fn answers_prefix(nums: Seq<i32>, queries: Seq<Vec<i32>>, t: int) -> Seq<i64>
        decreases t,
    {
        if t <= 0 {
            seq![]
        } else {
            let prev = Self::answers_prefix(nums, queries, t - 1);
            let marks = Self::state_after(nums, queries, t);
            prev.push(Self::sum_unmarked(nums, marks) as i64)
        }
    }

    proof fn lemma_best_prefix_unmarked(nums: Seq<i32>, marked: Seq<bool>, end: int)
        requires
            marked.len() == nums.len(),
            0 <= end <= nums.len(),
        ensures
            Self::best_in_prefix(nums, marked, end) == nums.len() as int
                || (0 <= Self::best_in_prefix(nums, marked, end) < end
                    && !marked[Self::best_in_prefix(nums, marked, end)]),
        decreases end,
    {
        if end > 0 {
            Self::lemma_best_prefix_unmarked(nums, marked, end - 1);
            let prev = Self::best_in_prefix(nums, marked, end - 1);
            let j = end - 1;
            if marked[j] {
            } else if prev == nums.len() as int || nums[j] < nums[prev] || (nums[j] == nums[prev] && j < prev) {
                assert(0 <= j < end);
                assert(!marked[j]);
            } else {
                if prev == nums.len() as int {
                } else {
                    assert(0 <= prev < end - 1);
                    assert(0 <= prev < end);
                }
            }
        }
    }

    pub fn unmarked_sum_array(nums: Vec<i32>, queries: Vec<Vec<i32>>) -> (result: Vec<i64>)
        requires
            1 <= queries.len() <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100_000,
            forall |i: int| 0 <= i < queries.len() ==> #[trigger] queries[i].len() == 2,
            forall |i: int| 0 <= i < queries.len() && queries[i].len() == 2 ==> 0 <= #[trigger] queries[i][0] < nums.len(),
            forall |i: int| 0 <= i < queries.len() && queries[i].len() == 2 ==> 0 <= #[trigger] queries[i][1] <= nums.len() - 1,
        ensures
            result@ == Self::answers_prefix(nums@, queries@, queries.len() as int),
    {
        let n = nums.len();

        let mut marked: Vec<bool> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                marked.len() == i,
                marked@ == Self::all_unmarked(i as int),
            decreases n - i,
        {
            marked.push(false);
            proof {
                assert(Self::all_unmarked((i + 1) as int) == Self::all_unmarked(i as int).push(false));
                assert(marked@ == Self::all_unmarked((i + 1) as int));
            }
            i = i + 1;
        }

        let mut result: Vec<i64> = Vec::new();
        let mut q: usize = 0;
        while q < queries.len()
            invariant
                0 <= q <= queries.len(),
                n == nums.len(),
                queries.len() >= 1,
                marked.len() == n,
                marked@ == Self::state_after(nums@, queries@, q as int),
                result@ == Self::answers_prefix(nums@, queries@, q as int),
                forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 100_000,
                forall |j: int| 0 <= j < queries.len() ==> #[trigger] queries[j].len() == 2,
                forall |j: int| 0 <= j < queries.len() && queries[j].len() == 2 ==> 0 <= #[trigger] queries[j][0] < nums.len(),
                forall |j: int| 0 <= j < queries.len() && queries[j].len() == 2 ==> 0 <= #[trigger] queries[j][1] <= nums.len() - 1,
            decreases queries.len() - q,
        {
            proof {
                assert(queries[q as int].len() == 2);
            }
            let idx_i32 = queries[q][0];
            let k = queries[q][1];
            proof {
                assert(0 <= idx_i32 < n as int);
            }
            let idx = idx_i32 as usize;
            proof {
                assert(idx as int == idx_i32 as int);
                assert(idx < n);
            }

            let ghost old_marked = marked@;
            if !marked[idx] {
                marked.set(idx, true);
                proof {
                    assert(marked@ == old_marked.update(idx as int, true));
                    assert(Self::mark_index(old_marked, idx as int) == old_marked.update(idx as int, true));
                }
            } else {
                proof {
                    assert(marked@ == old_marked);
                    assert(Self::mark_index(old_marked, idx as int) == old_marked);
                }
            }

            let ghost marked_after_index = marked@;
            let mut t: i32 = 0;
            while t < k
                invariant
                    0 <= t <= k,
                    n == nums.len(),
                    marked.len() == n,
                    marked@ == Self::mark_steps(nums@, marked_after_index, t as int),
                    forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 100_000,
                decreases k - t,
            {
                let mut best: usize = n;
                let mut j: usize = 0;
                while j < n
                    invariant
                        0 <= j <= n,
                        n == nums.len(),
                        marked.len() == n,
                        0 <= best <= n,
                        best as int == Self::best_in_prefix(nums@, marked@, j as int),
                    decreases n - j,
                {
                    let ghost old_best = best;
                    if !marked[j] {
                        if best == n {
                            best = j;
                        } else if nums[j] < nums[best] || (nums[j] == nums[best] && j < best) {
                            best = j;
                        }
                    }
                    proof {
                        let prev = Self::best_in_prefix(nums@, marked@, j as int);
                        let jj = j as int;
                        assert(Self::best_in_prefix(nums@, marked@, (j + 1) as int) == {
                            if marked[jj] {
                                prev
                            } else if prev == nums.len() as int || nums[jj] < nums[prev] || (nums[jj] == nums[prev] && jj < prev) {
                                jj
                            } else {
                                prev
                            }
                        });
                        if marked[jj] {
                            assert(best == old_best);
                        }
                    }
                    j = j + 1;
                }

                let ghost old_marked_t = marked@;
                if best < n {
                    proof {
                        Self::lemma_best_prefix_unmarked(nums@, old_marked_t, n as int);
                        assert(Self::best_unmarked(nums@, old_marked_t) == best as int);
                        assert(!old_marked_t[best as int]);
                    }
                    marked.set(best, true);
                    proof {
                        assert(marked@ == old_marked_t.update(best as int, true));
                    }
                } else {
                    proof {
                        assert(Self::best_unmarked(nums@, old_marked_t) == n as int);
                        assert(marked@ == old_marked_t);
                    }
                }

                proof {
                    assert(Self::mark_steps(nums@, marked_after_index, t as int + 1) == {
                        let prev = Self::mark_steps(nums@, marked_after_index, t as int);
                        let b = Self::best_unmarked(nums@, prev);
                        if b == nums.len() as int { prev } else { prev.update(b, true) }
                    });
                    assert(Self::mark_steps(nums@, marked_after_index, t as int) == old_marked_t);
                    assert(Self::best_unmarked(nums@, old_marked_t) == best as int);
                    if best < n {
                        assert(marked@ == old_marked_t.update(best as int, true));
                    } else {
                        assert(marked@ == old_marked_t);
                    }
                    assert(marked@ == Self::mark_steps(nums@, marked_after_index, t as int + 1));
                }
                t = t + 1;
            }

            let mut unmarked_sum: i128 = 0;
            let mut p: usize = 0;
            while p < n
                invariant
                    0 <= p <= n,
                    n == nums.len(),
                    marked.len() == n,
                    forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 100_000,
                    unmarked_sum as int == Self::sum_unmarked_prefix(nums@, marked@, p as int),
                    0 <= unmarked_sum as int <= 100_000 * p as int,
                decreases n - p,
            {
                let ghost old_sum = unmarked_sum as int;
                if !marked[p] {
                    unmarked_sum = unmarked_sum + nums[p] as i128;
                }
                proof {
                    assert(Self::sum_unmarked_prefix(nums@, marked@, (p + 1) as int)
                        == Self::sum_unmarked_prefix(nums@, marked@, p as int)
                            + if marked[p as int] { 0 } else { nums[p as int] as int });
                    if marked[p as int] {
                        assert(unmarked_sum as int == old_sum);
                    } else {
                        assert(unmarked_sum as int == old_sum + nums[p as int] as int);
                        assert(1 <= nums[p as int] <= 100_000);
                        assert(nums[p as int] as int <= 100_000);
                    }
                    assert(0 <= unmarked_sum as int <= 100_000 * (p as int + 1));
                }
                p = p + 1;
            }

            proof {
                assert(unmarked_sum as int == Self::sum_unmarked(nums@, marked@));
            }
            result.push(unmarked_sum as i64);
            proof {
                assert(t == k);
                assert(marked@ == Self::mark_steps(nums@, marked_after_index, k as int));
                assert(Self::mark_index(old_marked, idx as int) == marked_after_index);
                assert(Self::apply_query(nums@, old_marked, queries[q as int])
                    == Self::mark_steps(nums@, marked_after_index, k as int));
                assert(Self::state_after(nums@, queries@, q as int + 1)
                    == Self::apply_query(nums@, Self::state_after(nums@, queries@, q as int), queries[q as int]));
                assert(old_marked == Self::state_after(nums@, queries@, q as int));
                assert(marked@ == Self::state_after(nums@, queries@, q as int + 1));
                assert(result@ == Self::answers_prefix(nums@, queries@, q as int)
                    .push(Self::sum_unmarked(nums@, marked@) as i64));
                assert(Self::answers_prefix(nums@, queries@, q as int + 1)
                    == Self::answers_prefix(nums@, queries@, q as int)
                        .push(Self::sum_unmarked(nums@, Self::state_after(nums@, queries@, q as int + 1)) as i64));
            }

            q = q + 1;
        }

        result
    }
}

}
