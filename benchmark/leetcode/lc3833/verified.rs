use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn range_sum(nums: Seq<i32>, l: int, r: int) -> int
        recommends
            0 <= l <= r <= nums.len(),
        decreases r - l,
    {
        if l >= r {
            0
        } else {
            Self::range_sum(nums, l, r - 1) + nums[r - 1] as int
        }
    }

    pub open spec fn dominant_at(nums: Seq<i32>, i: int) -> bool {
        0 <= i < nums.len() - 1
            && nums[i] as int
                > Self::range_sum(nums, i + 1, nums.len() as int) / (nums.len() - i - 1)
    }

    pub open spec fn dominant_count_prefix(nums: Seq<i32>, k: nat) -> int
        recommends
            k <= nums.len(),
        decreases k,
    {
        if k == 0 {
            0
        } else {
            Self::dominant_count_prefix(nums, (k - 1) as nat)
                + if Self::dominant_at(nums, k as int - 1) { 1int } else { 0int }
        }
    }

    proof fn lemma_range_sum_step(nums: Seq<i32>, l: int, r: int)
        requires
            0 <= l <= r < nums.len(),
        ensures
            Self::range_sum(nums, l, r + 1) == Self::range_sum(nums, l, r) + nums[r] as int,
    {
    }

    proof fn lemma_dominant_count_step(nums: Seq<i32>, k: nat)
        requires
            k < nums.len(),
        ensures
            Self::dominant_count_prefix(nums, (k + 1) as nat)
                == Self::dominant_count_prefix(nums, k)
                    + if Self::dominant_at(nums, k as int) { 1int } else { 0int },
    {
    }

    pub fn dominant_indices(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 100,
            forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100,
        ensures
            res as int == Self::dominant_count_prefix(nums@, nums.len() as nat),
    {
        let n = nums.len();
        let mut ans: i32 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                n == nums.len(),
                1 <= nums.len() <= 100,
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100,
                0 <= i <= n,
                ans as int == Self::dominant_count_prefix(nums@, i as nat),
                0 <= ans as int,
                ans as int <= i as int,
            decreases n - i,
        {
            let ghost ans_before = ans;
            if i + 1 < n {
                let mut sum: i32 = 0;
                let mut j: usize = i + 1;
                while j < n
                    invariant
                        n == nums.len(),
                        1 <= nums.len() <= 100,
                        forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100,
                        0 <= i < n,
                        i + 1 <= j <= n,
                        sum as int == Self::range_sum(nums@, i as int + 1, j as int),
                        0 <= sum as int,
                        sum as int <= 100 * (j as int - i as int - 1),
                    decreases n - j,
                {
                    let ghost old_sum = sum;
                    let ghost old_j = j;
                    proof {
                        assert(0 <= old_j as int && (old_j as int) < nums.len());
                        assert(1 <= nums[old_j as int] && nums[old_j as int] <= 100);
                        assert(old_j as int <= n as int - 1);
                        assert(n as int <= 100);
                        assert(old_j as int - i as int - 1 <= 99);
                        assert(old_sum as int <= 100 * (old_j as int - i as int - 1));
                        assert(old_sum as int <= 9900);
                        assert(old_sum as int + nums[old_j as int] as int <= 10000);
                        Self::lemma_range_sum_step(nums@, i as int + 1, old_j as int);
                    }
                    sum = sum + nums[j];
                    j = j + 1;
                    proof {
                        assert(j as int == old_j as int + 1);
                        assert(sum as int == old_sum as int + nums[old_j as int] as int);
                        assert(old_sum as int == Self::range_sum(nums@, i as int + 1, old_j as int));
                        assert(sum as int == Self::range_sum(nums@, i as int + 1, j as int));
                        assert(sum as int <= 100 * (j as int - i as int - 1));
                    }
                }
                let right_len: i32 = (n - i - 1) as i32;
                let avg: i32 = sum / right_len;
                let is_dom: bool = nums[i] > avg;
                if nums[i] > avg {
                    ans = ans + 1;
                }
                proof {
                    assert(ans_before as int == Self::dominant_count_prefix(nums@, i as nat));
                    assert(i + 1 < n);
                    assert((n - i - 1) as int == n as int - i as int - 1);
                    assert(right_len as int == n as int - i as int - 1);
                    assert(right_len > 0);
                    assert(sum as int == Self::range_sum(nums@, i as int + 1, n as int));
                    assert(avg as int == sum as int / right_len as int);
                    if is_dom {
                        assert(nums[i as int] as int > avg as int);
                        assert(nums[i as int] as int > Self::range_sum(nums@, i as int + 1, n as int) / (n as int - i as int - 1));
                        assert(Self::dominant_at(nums@, i as int));
                        assert(ans as int == ans_before as int + 1);
                    } else {
                        assert(!(nums[i as int] as int > avg as int));
                        assert(nums[i as int] as int <= avg as int);
                        assert(nums[i as int] as int <= Self::range_sum(nums@, i as int + 1, n as int) / (n as int - i as int - 1));
                        assert(!Self::dominant_at(nums@, i as int));
                        assert(ans as int == ans_before as int);
                    }
                    Self::lemma_dominant_count_step(nums@, i as nat);
                    assert(ans as int == Self::dominant_count_prefix(nums@, (i + 1) as nat));
                    assert(ans as int <= i as int + 1);
                }
            } else {
                proof {
                    assert(i == n - 1);
                    assert(!(0 <= i as int && (i as int) < nums.len() - 1));
                    assert(!Self::dominant_at(nums@, i as int));
                    Self::lemma_dominant_count_step(nums@, i as nat);
                    assert(ans_before as int == Self::dominant_count_prefix(nums@, i as nat));
                    assert(ans as int == ans_before as int);
                    assert(ans as int == Self::dominant_count_prefix(nums@, (i + 1) as nat));
                    assert(ans as int <= i as int + 1);
                }
            }
            i = i + 1;
        }
        ans
    }
}

}
