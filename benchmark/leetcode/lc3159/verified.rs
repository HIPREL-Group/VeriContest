use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_x_prefix(nums: Seq<i32>, x: int, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::count_x_prefix(nums, x, end - 1)
                + if nums[end - 1] as int == x { 1int } else { 0int }
        }
    }

    pub open spec fn query_answer_ok(nums: Seq<i32>, x: int, k: int, value: int) -> bool {
        if value == -1 {
            Self::count_x_prefix(nums, x, nums.len() as int) < k
        } else {
            &&& 0 <= value < nums.len()
            &&& nums[value] as int == x
            &&& Self::count_x_prefix(nums, x, value) == k - 1
            &&& Self::count_x_prefix(nums, x, value + 1) == k
        }
    }

    pub open spec fn kth_occurrence_from(nums: Seq<i32>, x: int, k: int, idx: int, seen: int) -> int
        decreases nums.len() - idx,
    {
        if idx >= nums.len() {
            -1
        } else {
            let hit = if nums[idx] as int == x { 1int } else { 0int };
            let seen2 = seen + hit;
            if nums[idx] as int == x && seen2 == k {
                idx
            } else {
                Self::kth_occurrence_from(nums, x, k, idx + 1, seen2)
            }
        }
    }

    pub open spec fn kth_occurrence_index(nums: Seq<i32>, x: int, k: int) -> int {
        if k <= 0 { -1 } else { Self::kth_occurrence_from(nums, x, k, 0, 0) }
    }

    pub fn occurrences_of_element(nums: Vec<i32>, queries: Vec<i32>, x: i32) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 100000,
            1 <= queries.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 10000,
            forall |i: int| 0 <= i < queries.len() ==> 1 <= #[trigger] queries[i] <= 100000,
            1 <= x <= 10000,
        ensures
            result.len() == queries.len(),
            forall |qi: int| 0 <= qi < queries.len()
                ==> Self::query_answer_ok(nums@, x as int, queries[qi] as int, #[trigger] result[qi] as int),
    {
        let mut positions: Vec<i32> = Vec::new();
        let mut i = 0usize;
        while i < nums.len()
            invariant
                0 <= i <= nums.len(),
                nums.len() <= i32::MAX as usize,
                forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 10000,
                forall |r: int| 0 <= r < positions.len() ==> 0 <= #[trigger] positions[r] < nums.len(),
                forall |r: int| 0 <= r < positions.len() ==> nums[positions[r] as int] == x,
                positions.len() as int == Self::count_x_prefix(nums@, x as int, i as int),
                forall |r: int| 0 <= r < positions.len()
                    ==> Self::count_x_prefix(nums@, x as int, #[trigger] positions[r] as int) == r,
                forall |r: int| 0 <= r < positions.len()
                    ==> Self::count_x_prefix(nums@, x as int, #[trigger] positions[r] as int + 1) == r + 1,
                positions.len() <= i,
            decreases nums.len() - i,
        {
            if nums[i] == x {
                assert(i <= i32::MAX as usize);
                positions.push(i as i32);
                assert(0 <= positions[positions.len() as int - 1]);
                assert(positions[positions.len() as int - 1] < nums.len());
                assert(nums[positions[positions.len() as int - 1] as int] == x);
            }
            i += 1;
        }

        let mut ans: Vec<i32> = Vec::new();
        let mut j = 0usize;
        while j < queries.len()
            invariant
                0 <= j <= queries.len(),
                ans.len() == j,
                nums.len() <= i32::MAX as usize,
                forall |t: int| 0 <= t < queries.len() ==> 1 <= #[trigger] queries[t] <= 100000,
                forall |r: int| 0 <= r < positions.len() ==> 0 <= #[trigger] positions[r] < nums.len(),
                forall |r: int| 0 <= r < positions.len() ==> nums[positions[r] as int] == x,
                positions.len() as int == Self::count_x_prefix(nums@, x as int, nums.len() as int),
                forall |r: int| 0 <= r < positions.len()
                    ==> Self::count_x_prefix(nums@, x as int, #[trigger] positions[r] as int) == r,
                forall |r: int| 0 <= r < positions.len()
                    ==> Self::count_x_prefix(nums@, x as int, #[trigger] positions[r] as int + 1) == r + 1,
                forall |t: int| 0 <= t < j
                    ==> Self::query_answer_ok(nums@, x as int, queries[t] as int, #[trigger] ans[t] as int),
            decreases queries.len() - j,
        {
            let q = queries[j] as usize;
            if q == 0 || q > positions.len() {
                ans.push(-1);
                assert(Self::count_x_prefix(nums@, x as int, nums.len() as int) < queries[j as int] as int);
                assert(Self::query_answer_ok(nums@, x as int, queries[j as int] as int, -1));
            } else {
                ans.push(positions[q - 1]);
                assert(0 <= q as int - 1 < positions.len());
                assert(Self::count_x_prefix(nums@, x as int, positions[q as int - 1] as int) == queries[j as int] as int - 1);
                assert(Self::count_x_prefix(nums@, x as int, positions[q as int - 1] as int + 1) == queries[j as int] as int);
                assert(Self::query_answer_ok(nums@, x as int, queries[j as int] as int, positions[q as int - 1] as int));
            }
            j += 1;
        }
        ans
    }
}

}
