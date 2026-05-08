use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_occurrences(arr: Seq<i32>, left: int, right: int, val: i32) -> int
        decreases right - left + 1
    {
        if left > right {
            0
        } else if arr[left] == val {
            1 + Self::count_occurrences(arr, left + 1, right, val)
        } else {
            Self::count_occurrences(arr, left + 1, right, val)
        }
    }

    proof fn count_extend_right(arr: Seq<i32>, l: int, r: int, v: i32)
        requires
            0 <= l <= r,
            r < arr.len(),
        ensures
            Self::count_occurrences(arr, l, r, v) ==
                Self::count_occurrences(arr, l, r - 1, v) + if arr[r] == v { 1int } else { 0int }
        decreases r - l
    {
        if l == r {
            assert(Self::count_occurrences(arr, l + 1, l, v) == 0);
            assert(Self::count_occurrences(arr, l, l - 1, v) == 0);
        } else {
            Self::count_extend_right(arr, l + 1, r, v);
        }
    }

    proof fn count_non_negative(arr: Seq<i32>, l: int, r: int, v: i32)
        requires
            0 <= l,
            r < arr.len(),
        ensures
            Self::count_occurrences(arr, l, r, v) >= 0
        decreases r - l + 1
    {
        if l <= r {
            Self::count_non_negative(arr, l + 1, r, v);
        }
    }
}

pub struct MajorityChecker {
    pub arr: Vec<i32>,
}

impl MajorityChecker {
    pub fn new(arr: Vec<i32>) -> (result: Self)
        requires
            1 <= arr.len() <= 20_000,
            forall |i: int| 0 <= i < arr@.len() ==> 1 <= #[trigger] arr@[i] <= 20_000,
        ensures
            result.arr@ == arr@,
    {
        MajorityChecker { arr }
    }

    pub fn query(&self, left: i32, right: i32, threshold: i32) -> (result: i32)
        requires
            1 <= self.arr.len() <= 20_000,
            forall |i: int| 0 <= i < self.arr@.len() ==> 1 <= #[trigger] self.arr@[i] <= 20_000,
            0 <= left <= right,
            right < self.arr.len() as i32,
            threshold >= 1,
            threshold <= right - left + 1,
            2 * threshold > right - left + 1,
        ensures
            result == -1 || (
                1 <= result <= 20_000
                && Solution::count_occurrences(self.arr@, left as int, right as int, result) >= threshold as int
            ),
            result == -1 ==> forall |v: i32| 1 <= v <= 20_000 ==>
                Solution::count_occurrences(self.arr@, left as int, right as int, v) < threshold as int,
    {
        let l = left as usize;
        let r = right as usize;
        let mut candidate: i32 = self.arr[l];
        let mut cnt: i32 = 0;
        let mut i: usize = l;
        while i <= r
            invariant
                l as int == left as int,
                r as int == right as int,
                0 <= left <= right,
                right < self.arr.len() as i32,
                1 <= self.arr.len() <= 20_000,
                forall |k: int| 0 <= k < self.arr@.len() ==> 1 <= #[trigger] self.arr@[k] <= 20_000,
                l <= i <= r + 1,
                cnt >= 0,
                cnt <= i as int - l as int,
                1 <= candidate <= 20_000,
                forall |v: i32| 1 <= v <= 20_000 && v != candidate ==>
                    2 * (#[trigger] Solution::count_occurrences(self.arr@, l as int, (i as int) - 1, v))
                        <= i as int - l as int - cnt as int,
                2 * Solution::count_occurrences(self.arr@, l as int, (i as int) - 1, candidate)
                    <= i as int - l as int + cnt as int,
            decreases r + 1 - i
        {
            let ghost old_candidate = candidate;
            let ghost old_cnt = cnt;

            if cnt == 0 {
                candidate = self.arr[i];
                cnt = 1;
            } else if self.arr[i] == candidate {
                cnt = cnt + 1;
            } else {
                cnt = cnt - 1;
            }

            proof {
                assert forall |v: i32| 1 <= v <= 20_000 && v != candidate implies
                    2 * (#[trigger] Solution::count_occurrences(self.arr@, l as int, i as int, v))
                        <= (i + 1) as int - l as int - cnt as int
                by {
                    Solution::count_extend_right(self.arr@, l as int, i as int, v);
                    Solution::count_non_negative(self.arr@, l as int, (i as int) - 1, v);
                };

                Solution::count_extend_right(self.arr@, l as int, i as int, candidate);
                Solution::count_non_negative(self.arr@, l as int, (i as int) - 1, candidate);
            }

            i = i + 1;
        }

        let ghost bm_cnt = cnt;

        let mut actual_count: i32 = 0;
        let mut j: usize = l;
        while j <= r
            invariant
                l as int == left as int,
                r as int == right as int,
                0 <= left <= right,
                right < self.arr.len() as i32,
                1 <= self.arr.len() <= 20_000,
                forall |k: int| 0 <= k < self.arr@.len() ==> 1 <= #[trigger] self.arr@[k] <= 20_000,
                l <= j <= r + 1,
                1 <= candidate <= 20_000,
                actual_count >= 0,
                actual_count as int == Solution::count_occurrences(self.arr@, l as int, (j as int) - 1, candidate),
                actual_count <= (j - l) as i32,
                cnt == bm_cnt,
                bm_cnt >= 0,
                forall |v: i32| 1 <= v <= 20_000 && v != candidate ==>
                    2 * (#[trigger] Solution::count_occurrences(self.arr@, l as int, r as int, v))
                        <= r as int + 1 - l as int - bm_cnt as int,
            decreases r + 1 - j
        {
            proof {
                Solution::count_extend_right(self.arr@, l as int, j as int, candidate);
            }
            if self.arr[j] == candidate {
                actual_count = actual_count + 1;
            }
            j = j + 1;
        }

        if actual_count >= threshold {
            candidate
        } else {
            proof {
                assert forall |v: i32| 1 <= v <= 20_000 implies
                    (#[trigger] Solution::count_occurrences(self.arr@, l as int, r as int, v)) < threshold as int
                by {
                    if v == candidate {
                    } else {
                        Solution::count_non_negative(self.arr@, l as int, r as int, v);
                    }
                };
            }
            -1
        }
    }
}

}
