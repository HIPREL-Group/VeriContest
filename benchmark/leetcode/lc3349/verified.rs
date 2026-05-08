use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_strictly_increasing(nums: Seq<i32>, start: int, len: int) -> bool {
        1 <= len
        && 0 <= start
        && start + len <= nums.len()
        && forall |j: int| start <= j < start + len - 1 ==> #[trigger] nums[j] < nums[j + 1]
    }

    pub open spec fn adjacent_pair_at(nums: Seq<i32>, a: int, k: int) -> bool {
        1 <= k
        && 0 <= a
        && a + 2 * k <= nums.len()
        && Self::is_strictly_increasing(nums, a, k)
        && Self::is_strictly_increasing(nums, a + k, k)
    }

    pub open spec fn has_adjacent_increasing_subarrays(nums: Seq<i32>, k: int) -> bool {
        1 <= k
        && exists |a: int| #[trigger] Self::adjacent_pair_at(nums, a, k)
    }

    proof fn lemma_subsegment_of_increasing(nums: Seq<i32>, start: int, len: int, sub_start: int, sub_len: int)
        requires
            Self::is_strictly_increasing(nums, start, len),
            start <= sub_start,
            1 <= sub_len,
            sub_start + sub_len <= start + len,
        ensures
            Self::is_strictly_increasing(nums, sub_start, sub_len),
    {
        assert(0 <= sub_start);
        assert(sub_start + sub_len <= nums.len());
        assert forall |j: int| sub_start <= j < sub_start + sub_len - 1 implies #[trigger] nums[j] < nums[j + 1] by {
            assert(start <= j);
            assert(j < start + len - 1);
        };
    }

    proof fn lemma_has_for_smaller(nums: Seq<i32>, k_big: int, k_small: int)
        requires
            Self::has_adjacent_increasing_subarrays(nums, k_big),
            1 <= k_small <= k_big,
        ensures
            Self::has_adjacent_increasing_subarrays(nums, k_small),
    {
        let a = choose |a: int| #[trigger] Self::adjacent_pair_at(nums, a, k_big);
        let start_small = a + (k_big - k_small);
        assert(0 <= a);
        assert(a + 2 * k_big <= nums.len());
        assert(0 <= start_small);
        assert(start_small + k_small <= a + k_big);
        assert(a + k_big + k_small <= a + 2 * k_big);
        Self::lemma_subsegment_of_increasing(nums, a, k_big, start_small, k_small);
        Self::lemma_subsegment_of_increasing(nums, a + k_big, k_big, a + k_big, k_small);
        assert(Self::has_adjacent_increasing_subarrays(nums, k_small)) by {
            assert(Self::adjacent_pair_at(nums, start_small, k_small));
        };
    }

    fn max_increasing_subarrays(nums: &Vec<i32>) -> (result: i32)
        requires
            2 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
        ensures
            1 <= result as int,
            2 * result as int <= nums.len(),
            Self::has_adjacent_increasing_subarrays(nums@, result as int),
            forall |k: int| 1 <= k <= nums.len() / 2 && #[trigger] Self::has_adjacent_increasing_subarrays(nums@, k)
                ==> k <= result as int,
    {
        let n = nums.len();
        let mut prev = 0usize;
        let mut curr = 1usize;
        let mut ans = 0usize;
        let mut start = 0usize;
        let ghost mut best_a: int = 0;
        let mut i = 1usize;

        while i < n
            invariant
                2 <= n <= 100,
                n == nums.len(),
                1 <= i <= n,
                0 <= start < i,
                0 <= prev <= start,
                curr == i - start,
                1 <= curr,
                start == 0 ==> prev == 0,
                start > 0 ==> 1 <= prev <= start,
                forall |j: int| start as int <= j < i as int - 1 ==> #[trigger] nums@[j] < nums@[j + 1],
                start > 0 ==> nums@[start as int - 1] >= nums@[start as int],
                start > 0 ==> forall |j: int| (start - prev) as int <= j < start as int - 1 ==> #[trigger] nums@[j] < nums@[j + 1],
                start > prev ==> nums@[(start - prev) as int - 1] >= nums@[(start - prev) as int],
                2 * ans as int <= i as int,
                ans > 0 ==> 0 <= best_a && best_a + 2 * ans as int <= i as int,
                ans > 0 ==> Self::is_strictly_increasing(nums@, best_a, ans as int),
                ans > 0 ==> Self::is_strictly_increasing(nums@, best_a + ans as int, ans as int),
                forall |a: int, k: int|
                    #[trigger] Self::adjacent_pair_at(nums@, a, k)
                    && a + 2 * k <= i as int
                    ==> k <= ans as int,
            decreases n - i,
        {
            let ghost old_start = start as int;
            let ghost old_prev = prev as int;
            let ghost old_curr = curr as int;
            let ghost old_ans = ans as int;
            let ghost old_best_a = best_a;

            proof {
                assert(old_curr == i as int - old_start);
                assert forall |j: int| old_start <= j < i as int - 1 implies #[trigger] nums@[j] < nums@[j + 1] by {
                    assert(nums@[j] < nums@[j + 1]);
                };
                assert forall |a: int, k: int|
                    #[trigger] Self::adjacent_pair_at(nums@, a, k)
                    && a + 2 * k <= i as int
                    implies k <= old_ans by {
                    assert(k <= ans as int);
                };
                if old_ans > 0 {
                    assert(0 <= old_best_a && old_best_a + 2 * old_ans <= i as int);
                    assert(Self::is_strictly_increasing(nums@, old_best_a, old_ans));
                    assert(Self::is_strictly_increasing(nums@, old_best_a + old_ans, old_ans));
                }
                if old_start > 0 {
                    assert(nums@[old_start - 1] >= nums@[old_start]);
                    assert(1 <= old_prev <= old_start);
                    assert forall |j: int| old_start - old_prev <= j < old_start - 1 implies #[trigger] nums@[j] < nums@[j + 1] by {
                        assert(nums@[j] < nums@[j + 1]);
                    };
                    if old_start > old_prev {
                        assert(nums@[old_start - old_prev - 1] >= nums@[old_start - old_prev]);
                    }
                }
            }

            if nums[i] > nums[i - 1] {
                curr = curr + 1;
                proof {
                    assert(start as int == old_start);
                    assert(curr as int == i as int + 1 - start as int);
                    assert forall |j: int| start as int <= j < i as int implies #[trigger] nums@[j] < nums@[j + 1] by {
                        if j < i as int - 1 {
                            assert(old_start <= j < i as int - 1);
                        } else {
                            assert(j == i as int - 1);
                            assert(nums@[i as int - 1] < nums@[i as int]);
                        }
                    };
                }
            } else {
                prev = curr;
                start = i;
                curr = 1;
                proof {
                    assert(prev as int == old_curr);
                    assert(start as int - prev as int == old_start);
                    assert(curr as int == i as int + 1 - start as int);
                    assert(nums@[start as int - 1] >= nums@[start as int]);
                    assert forall |j: int| (start - prev) as int <= j < start as int - 1 implies #[trigger] nums@[j] < nums@[j + 1] by {
                        assert(old_start <= j < i as int - 1);
                    };
                    if start > prev {
                        assert(start as int - prev as int > 0);
                        assert(nums@[(start - prev) as int - 1] >= nums@[(start - prev) as int]);
                    }
                }
            }

            let split = curr / 2;
            let cross = if prev < curr { prev } else { curr };
            let mut next_ans = ans;
            let ghost mut next_best_a = best_a;

            if split > next_ans {
                proof {
                    assert(1 <= split as int);
                    assert(2 * split as int <= curr as int) by (nonlinear_arith)
                        requires
                            split == curr / 2,
                    {};
                    Self::lemma_subsegment_of_increasing(nums@, start as int, curr as int, start as int, split as int);
                    Self::lemma_subsegment_of_increasing(nums@, start as int, curr as int, start as int + split as int, split as int);
                    next_best_a = start as int;
                }
                next_ans = split;
            }

            if cross > next_ans {
                proof {
                    assert(1 <= cross as int);
                    assert(start > 0);
                    assert(cross as int <= prev as int);
                    assert(cross as int <= curr as int);
                    assert(0 <= start as int - cross as int);
                    Self::lemma_subsegment_of_increasing(
                        nums@,
                        start as int - prev as int,
                        prev as int,
                        start as int - cross as int,
                        cross as int,
                    );
                    Self::lemma_subsegment_of_increasing(nums@, start as int, curr as int, start as int, cross as int);
                    next_best_a = start as int - cross as int;
                }
                next_ans = cross;
            }

            proof {
                assert(next_ans as int >= old_ans);
                assert(next_ans as int >= split as int);
                assert(next_ans as int >= cross as int);
                if next_ans > 0 {
                    if next_ans as int == old_ans {
                        assert(0 <= next_best_a && next_best_a + 2 * next_ans as int <= i as int + 1);
                        assert(Self::is_strictly_increasing(nums@, next_best_a, next_ans as int));
                        assert(Self::is_strictly_increasing(nums@, next_best_a + next_ans as int, next_ans as int));
                    } else if next_ans == split {
                        assert(next_best_a == start as int);
                        assert(0 <= next_best_a);
                        assert(start as int + 2 * split as int <= start as int + curr as int);
                        assert(start as int + curr as int == i as int + 1);
                        assert(next_best_a + 2 * next_ans as int <= i as int + 1);
                    } else {
                        assert(next_ans == cross);
                        assert(next_best_a == start as int - cross as int);
                        assert(0 <= next_best_a);
                        assert(start as int + cross as int <= start as int + curr as int);
                        assert(start as int + curr as int == i as int + 1);
                        assert(next_best_a + 2 * next_ans as int == start as int + cross as int);
                        assert(next_best_a + 2 * next_ans as int <= i as int + 1);
                    }
                }

                assert forall |a: int, k: int|
                    #[trigger] Self::adjacent_pair_at(nums@, a, k)
                    && a + 2 * k <= i as int + 1
                    implies k <= next_ans as int by {
                    if a + 2 * k <= i as int {
                        assert(k <= old_ans);
                        assert(old_ans <= next_ans as int);
                    } else {
                        assert(a + 2 * k == i as int + 1);
                        let second_start = a + k;
                        if second_start < start as int {
                            assert(second_start <= start as int - 1);
                            assert(start as int <= second_start + k - 1);
                            assert(nums@[start as int - 1] < nums@[start as int]);
                            assert(start > 0);
                            assert(nums@[start as int - 1] >= nums@[start as int]);
                            assert(false);
                        }
                        if a >= start as int {
                            assert(2 * k <= curr as int) by (nonlinear_arith)
                                requires
                                    a + 2 * k == i as int + 1,
                                    a >= start as int,
                                    curr as int == i as int + 1 - start as int,
                        {};
                            assert(k <= split as int) by (nonlinear_arith)
                                requires
                                    split == curr / 2,
                                    2 * k <= curr as int,
                        {};
                            assert(split as int <= next_ans as int);
                        } else {
                            assert(second_start >= start as int);
                            if second_start > start as int {
                                assert(a <= start as int - 1);
                                assert(start as int <= a + k - 1);
                                assert(nums@[start as int - 1] < nums@[start as int]);
                                assert(start > 0);
                                assert(nums@[start as int - 1] >= nums@[start as int]);
                                assert(false);
                            }
                            assert(second_start == start as int);
                            if a < start as int - prev as int {
                                if start as int - prev as int > 0 {
                                    assert(a <= start as int - prev as int - 1);
                                    assert(start as int - prev as int <= a + k - 1) by (nonlinear_arith)
                                        requires
                                            a + k == start as int,
                                            a < start as int - prev as int,
                                            1 <= prev as int,
                                {};
                                    assert(nums@[start as int - prev as int - 1] < nums@[start as int - prev as int]);
                                    assert(nums@[start as int - prev as int - 1] >= nums@[start as int - prev as int]);
                                    assert(false);
                                } else {
                                    assert(a < 0);
                                    assert(false);
                                }
                            }
                            assert(k == start as int - a);
                            assert(k <= prev as int);
                            assert(k <= curr as int) by (nonlinear_arith)
                                requires
                                    a + 2 * k == i as int + 1,
                                    a + k == start as int,
                                    curr as int == i as int + 1 - start as int,
                            {};
                            assert(k <= cross as int);
                            assert(cross as int <= next_ans as int);
                        }
                    }
                };
            }

            ans = next_ans;
            proof {
                best_a = next_best_a;
            }
            i = i + 1;
        }

        proof {
            assert(Self::is_strictly_increasing(nums@, 0, 1));
            assert(Self::is_strictly_increasing(nums@, 1, 1));
            assert(Self::has_adjacent_increasing_subarrays(nums@, 1)) by {
                let a = 0int;
                assert(Self::adjacent_pair_at(nums@, a, 1));
            };
            assert(1 <= ans as int) by {
                assert(0 + 2 * 1 <= n as int);
                assert(Self::is_strictly_increasing(nums@, 0, 1));
                assert(Self::is_strictly_increasing(nums@, 1, 1));
            }
            assert(Self::has_adjacent_increasing_subarrays(nums@, ans as int)) by {
                assert(ans > 0);
                assert(Self::adjacent_pair_at(nums@, best_a, ans as int));
            };
            assert forall |k: int| 1 <= k <= nums.len() / 2 && #[trigger] Self::has_adjacent_increasing_subarrays(nums@, k)
                implies k <= ans as int by {
                let a = choose |a: int|
                    Self::adjacent_pair_at(nums@, a, k);
                assert(a + 2 * k <= n as int);
                assert(k <= ans as int);
            };
        }

        ans as i32
    }


    pub fn has_increasing_subarrays(nums: Vec<i32>, k: i32) -> (result: bool)
        requires
            2 <= nums.len() <= 100,
            1 < 2 * k as int,
            2 * k as int <= nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
        ensures
            result <==> Self::has_adjacent_increasing_subarrays(nums@, k as int),
    {
        let best = Self::max_increasing_subarrays(&nums);
        proof {
            assert(1 <= k as int);
            if best >= k {
                Self::lemma_has_for_smaller(nums@, best as int, k as int);
            } else {
                assert(!(Self::has_adjacent_increasing_subarrays(nums@, k as int))) by {
                    if Self::has_adjacent_increasing_subarrays(nums@, k as int) {
                        assert(k as int <= best as int);
                        assert(false);
                    }
                };
            }
        }
        best >= k
    }
}

}