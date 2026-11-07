use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_non_decreasing(s: Seq<i32>) -> bool {
        forall |i: int| 0 < i && i < s.len() ==> s[i - 1] <= #[trigger] s[i]
    }

    pub open spec fn pair_sum(s: Seq<i32>, i: int) -> int {
        if 0 <= i && i + 1 < s.len() {
            s[i] as int + s[i + 1] as int
        } else {
            0
        }
    }

    pub open spec fn pair_sum_i32(s: Seq<i32>, i: int) -> i32 {
        if 0 <= i && i + 1 < s.len() {
            ((s[i] as i64 + s[i + 1] as i64) as i32)
        } else {
            0
        }
    }

    pub open spec fn min_index_prefix(s: Seq<i32>, upto: int) -> int
        decreases upto,
    {
        if s.len() < 2 || upto <= 1 {
            0
        } else {
            let prev = Self::min_index_prefix(s, upto - 1);
            let cur = upto - 1;
            if Self::pair_sum(s, cur) < Self::pair_sum(s, prev) {
                cur
            } else {
                prev
            }
        }
    }

    pub open spec fn min_pair_index(s: Seq<i32>) -> int {
        if s.len() < 2 {
            0
        } else {
            Self::min_index_prefix(s, s.len() - 1)
        }
    }

    pub open spec fn merge_at(s: Seq<i32>, idx: int) -> Seq<i32> {
        if s.len() < 2 {
            s
        } else if 0 <= idx && idx + 1 < s.len() {
            s.subrange(0, idx) + seq![Self::pair_sum_i32(s, idx)] + s.subrange(idx + 2, s.len() as int)
        } else {
            s.subrange(0, 0) + seq![Self::pair_sum_i32(s, 0)] + s.subrange(2, s.len() as int)
        }
    }

    pub open spec fn next_seq(s: Seq<i32>) -> Seq<i32> {
        if s.len() < 2 {
            s
        } else {
            Self::merge_at(s, Self::min_pair_index(s))
        }
    }

    pub open spec fn steps_to_sort_fuel(s: Seq<i32>, fuel: nat) -> nat
        decreases fuel,
    {
        if fuel == 0 || s.len() <= 1 || Self::is_non_decreasing(s) {
            0
        } else {
            1nat + Self::steps_to_sort_fuel(Self::next_seq(s), (fuel - 1) as nat)
        }
    }

    pub open spec fn steps_to_sort(s: Seq<i32>) -> nat {
        Self::steps_to_sort_fuel(s, s.len() as nat)
    }

    proof fn lemma_not_non_decreasing_len_ge_2(s: Seq<i32>)
        requires
            !Self::is_non_decreasing(s),
        ensures
            s.len() >= 2,
    {
        if s.len() <= 1 {
            assert(Self::is_non_decreasing(s));
            assert(false);
        }
    }

    proof fn lemma_subrange_extend(s: Seq<i32>, start: int, end: int)
        requires
            0 <= start <= end < s.len(),
        ensures
            s.subrange(start, end + 1) =~= s.subrange(start, end).push(s[end]),
    {
        assert(s.subrange(start, end + 1).len() == s.subrange(start, end).push(s[end]).len());
        assert forall |k: int| 0 <= k && k < s.subrange(start, end + 1).len() implies
            s.subrange(start, end + 1)[k] == s.subrange(start, end).push(s[end])[k] by {
            if k < s.subrange(start, end).len() {
                assert(s.subrange(start, end)[k] == s[start + k]);
                assert(s.subrange(start, end + 1)[k] == s[start + k]);
                assert(s.subrange(start, end).push(s[end])[k] == s.subrange(start, end)[k]);
            } else {
                assert(k == s.subrange(start, end).len());
                assert(s.subrange(start, end + 1)[k] == s[end]);
                assert(s.subrange(start, end).push(s[end])[k] == s[end]);
            }
        };
    }

    proof fn lemma_merge_len_valid(s: Seq<i32>, idx: int)
        requires
            s.len() >= 2,
            0 <= idx,
            idx + 1 < s.len(),
        ensures
            Self::merge_at(s, idx).len() == s.len() - 1,
    {
    }

    fn is_non_decreasing_vec(arr: &Vec<i32>) -> (res: bool)
        ensures
            res == Self::is_non_decreasing(arr@),
    {
        if arr.len() <= 1 {
            proof {
                assert(Self::is_non_decreasing(arr@));
            }
            return true;
        }
        let mut i: usize = 1;
        while i < arr.len()
            invariant
                1 <= i <= arr.len(),
                forall |k: int| 1 <= k && k < i as int ==> arr@[k - 1] <= #[trigger] arr@[k],
            decreases arr.len() - i,
        {
            if arr[i - 1] > arr[i] {
                proof {
                    assert(arr@[i as int - 1] > arr@[i as int]);
                    assert(!Self::is_non_decreasing(arr@));
                }
                return false;
            }
            i += 1;
        }
        proof {
            assert forall |k: int| 0 < k && k < arr.len() implies arr@[k - 1] <= #[trigger] arr@[k] by {
                assert(1 <= k && k < i as int);
            };
            assert(Self::is_non_decreasing(arr@));
        }
        true
    }

    pub fn minimum_pair_removal(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 50,
            forall |i: int| 0 <= i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
        ensures
            result as int == Self::steps_to_sort(nums@) as int,
    {
        let mut arr = nums;
        let mut ops: usize = 0;
        let mut sorted = Self::is_non_decreasing_vec(&arr);

        while !sorted
            invariant
                1 <= arr.len() <= nums.len(),
                ops <= nums.len(),
                sorted == Self::is_non_decreasing(arr@),
                ops as int + arr.len() as int == nums.len() as int,
                ops as int + Self::steps_to_sort(arr@) as int == Self::steps_to_sort(nums@) as int,
            decreases arr.len(),
        {
            proof {
                assert(!Self::is_non_decreasing(arr@));
                Self::lemma_not_non_decreasing_len_ge_2(arr@);
            }

            let n = arr.len();
            let mut best_idx: usize = 0;
            let mut best_sum: i64 = arr[0] as i64 + arr[1] as i64;
            let mut i: usize = 1;
            while i < n - 1
                invariant
                    n == arr.len(),
                    2 <= n,
                    1 <= i <= n - 1,
                    0 <= best_idx < i,
                    best_idx as int == Self::min_index_prefix(arr@, i as int),
                    best_sum as int == Self::pair_sum(arr@, best_idx as int),
                decreases n - 1 - i,
            {
                let cur_sum: i64 = arr[i] as i64 + arr[i + 1] as i64;
                proof {
                    assert(cur_sum as int == Self::pair_sum(arr@, i as int));
                    assert(Self::min_index_prefix(arr@, i as int + 1)
                        == if Self::pair_sum(arr@, i as int) < Self::pair_sum(arr@, Self::min_index_prefix(arr@, i as int)) {
                            i as int
                        } else {
                            Self::min_index_prefix(arr@, i as int)
                        });
                }
                if cur_sum < best_sum {
                    proof {
                        assert(Self::pair_sum(arr@, i as int) < Self::pair_sum(arr@, Self::min_index_prefix(arr@, i as int)));
                        assert(Self::min_index_prefix(arr@, i as int + 1) == i as int);
                    }
                    best_idx = i;
                    best_sum = cur_sum;
                } else {
                    proof {
                        assert(Self::pair_sum(arr@, i as int) >= Self::pair_sum(arr@, Self::min_index_prefix(arr@, i as int)));
                        assert(Self::min_index_prefix(arr@, i as int + 1) == Self::min_index_prefix(arr@, i as int));
                    }
                }
                i += 1;
            }

            proof {
                assert(i == n - 1);
                assert(best_idx as int == Self::min_pair_index(arr@));
            }

            let ghost old_arr = arr@;
            let ghost old_ops = ops as int;
            let mut next_arr: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < best_idx
                invariant
                    n == arr.len(),
                    old_arr == arr@,
                    0 <= j <= best_idx,
                    best_idx <= n - 2,
                    next_arr@ =~= old_arr.subrange(0, j as int),
                decreases best_idx - j,
            {
                let ghost prev = next_arr@;
                next_arr.push(arr[j]);
                proof {
                    Self::lemma_subrange_extend(old_arr, 0, j as int);
                    assert(old_arr.subrange(0, j as int + 1) =~= old_arr.subrange(0, j as int).push(old_arr[j as int]));
                    assert(next_arr@ =~= prev.push(arr[j as int]));
                    assert(arr[j as int] == old_arr[j as int]);
                    assert(next_arr@ =~= old_arr.subrange(0, j as int + 1));
                }
                j += 1;
            }

            #[verifier::truncate]
            let merged = (arr[best_idx] as i64 + arr[best_idx + 1] as i64) as i32;
            let ghost prev_prefix = next_arr@;
            next_arr.push(merged);
            proof {
                assert(best_idx + 1 < n);
                assert(prev_prefix =~= old_arr.subrange(0, best_idx as int));
                assert(arr[best_idx as int] == old_arr[best_idx as int]);
                assert(arr[best_idx as int + 1] == old_arr[best_idx as int + 1]);
                assert(merged == Self::pair_sum_i32(old_arr, best_idx as int));
                assert(next_arr@ =~= prev_prefix.push(merged));
                assert(next_arr@ =~= old_arr.subrange(0, best_idx as int) + seq![merged]);
            }

            j = best_idx + 2;
            while j < n
                invariant
                    n == arr.len(),
                    old_arr == arr@,
                    best_idx <= n - 2,
                    best_idx + 2 <= j <= n,
                    merged == Self::pair_sum_i32(old_arr, best_idx as int),
                    next_arr@ =~= old_arr.subrange(0, best_idx as int)
                        + seq![merged]
                        + old_arr.subrange((best_idx + 2) as int, j as int),
                decreases n - j,
            {
                let ghost prev = next_arr@;
                next_arr.push(arr[j]);
                proof {
                    Self::lemma_subrange_extend(old_arr, (best_idx + 2) as int, j as int);
                    assert(old_arr.subrange((best_idx + 2) as int, j as int + 1)
                        =~= old_arr.subrange((best_idx + 2) as int, j as int).push(old_arr[j as int]));
                    assert(next_arr@ =~= prev.push(arr[j as int]));
                    assert(arr[j as int] == old_arr[j as int]);
                    assert(next_arr@ =~= old_arr.subrange(0, best_idx as int)
                        + seq![merged]
                        + old_arr.subrange((best_idx + 2) as int, j as int + 1));
                }
                j += 1;
            }

            proof {
                assert(next_arr@ =~= old_arr.subrange(0, best_idx as int)
                    + seq![merged]
                    + old_arr.subrange((best_idx + 2) as int, n as int));
                assert(next_arr@ =~= old_arr.subrange(0, best_idx as int)
                    + seq![Self::pair_sum_i32(old_arr, best_idx as int)]
                    + old_arr.subrange((best_idx + 2) as int, n as int));
                assert(next_arr@ =~= Self::merge_at(old_arr, best_idx as int));
                assert(next_arr@ =~= Self::next_seq(old_arr));
                Self::lemma_merge_len_valid(old_arr, best_idx as int);
                assert(next_arr.len() as int == old_arr.len() - 1);
                assert(Self::steps_to_sort(old_arr) == Self::steps_to_sort_fuel(old_arr, old_arr.len() as nat));
                assert(Self::steps_to_sort(old_arr)
                    == 1nat + Self::steps_to_sort_fuel(Self::next_seq(old_arr), (old_arr.len() as nat - 1nat) as nat));
                assert(Self::steps_to_sort_fuel(Self::next_seq(old_arr), (old_arr.len() as nat - 1nat) as nat)
                    == Self::steps_to_sort_fuel(next_arr@, next_arr.len() as nat));
                assert(Self::steps_to_sort_fuel(next_arr@, next_arr.len() as nat) == Self::steps_to_sort(next_arr@));
                assert(Self::steps_to_sort(old_arr) as int == 1 + Self::steps_to_sort(next_arr@) as int);
                assert(old_ops + 1 + Self::steps_to_sort(next_arr@) as int == Self::steps_to_sort(nums@) as int);
                assert(old_ops + 1 <= nums.len() as int);
            }

            arr = next_arr;
            ops += 1;
            sorted = Self::is_non_decreasing_vec(&arr);
        }

        proof {
            assert(sorted == Self::is_non_decreasing(arr@));
            assert(Self::steps_to_sort(arr@) == 0);
            assert(ops as int == Self::steps_to_sort(nums@) as int);
            assert(ops <= nums.len());
            assert(nums.len() <= 50);
            assert(ops as int <= 50);
        }

        ops as i32
    }
}

}
