use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_strictly_increasing(nums: Seq<i32>, start: int, len: int) -> bool
    {
        forall |j: int| start <= j < start + len - 1 ==> #[trigger] nums[j] < nums[j + 1]
    }

    spec fn run_at(nums: Seq<i32>, i: int) -> nat
        decreases i,
    {
        if i <= 0 {
            1
        } else if nums[i] > nums[i - 1] {
            Self::run_at(nums, i - 1) + 1
        } else {
            1
        }
    }

    spec fn max_run(nums: Seq<i32>, i: int) -> nat
        decreases i,
    {
        if i <= 0 {
            Self::run_at(nums, 0)
        } else {
            let prev = Self::max_run(nums, i - 1);
            let cur  = Self::run_at(nums, i);
            if cur > prev { cur } else { prev }
        }
    }

    proof fn lemma_run_at_pos(nums: Seq<i32>, i: int)
        requires 0 <= i < nums.len(),
        ensures  Self::run_at(nums, i) >= 1,
        decreases i,
    {
        if i > 0 && nums[i] > nums[i - 1] {
            Self::lemma_run_at_pos(nums, i - 1);
        }
    }

    proof fn lemma_run_at_bound(nums: Seq<i32>, i: int)
        requires 0 <= i < nums.len(),
        ensures  Self::run_at(nums, i) <= i + 1,
        decreases i,
    {
        if i > 0 && nums[i] > nums[i - 1] {
            Self::lemma_run_at_bound(nums, i - 1);
        }
    }

    proof fn lemma_run_at_inner(nums: Seq<i32>, i: int, j: int)
        requires
            0 <= i < nums.len(),
            i - Self::run_at(nums, i) as int + 1 <= j < i,
        ensures  nums[j] < nums[j + 1],
        decreases i,
    {
        if i > 0 && nums[i] > nums[i - 1] {
            let start      = i - Self::run_at(nums, i) as int + 1;
            let start_prev = (i - 1) - Self::run_at(nums, i - 1) as int + 1;
            assert(start == start_prev);
            if j < i - 1 {
                Self::lemma_run_at_inner(nums, i - 1, j);
            }
        }
    }

    proof fn lemma_run_at_increasing(nums: Seq<i32>, i: int)
        requires 0 <= i < nums.len(),
        ensures  Self::is_strictly_increasing(
                     nums,
                     i - Self::run_at(nums, i) as int + 1,
                     Self::run_at(nums, i) as int,
                 ),
    {
        let start = i - Self::run_at(nums, i) as int + 1;
        assert forall |j: int| start <= j < i implies #[trigger] nums[j] < nums[j + 1] by {
            Self::lemma_run_at_inner(nums, i, j);
        }
    }

    proof fn lemma_increasing_implies_run_at(nums: Seq<i32>, start: int, end: int)
        requires
            0 <= start < end <= nums.len(),
            Self::is_strictly_increasing(nums, start, end - start),
        ensures  Self::run_at(nums, end - 1) >= (end - start) as nat,
        decreases end - start,
    {
        if end - start == 1 {
            Self::lemma_run_at_pos(nums, end - 1);
        } else {
            assert(Self::is_strictly_increasing(nums, start, end - start - 1)) by {
                assert forall |j: int| start <= j < end - 2 implies #[trigger] nums[j] < nums[j + 1] by {
                    assert(nums[j] < nums[j + 1]);
                }
            };
            Self::lemma_increasing_implies_run_at(nums, start, end - 1);
        }
    }

    proof fn lemma_max_run_ge(nums: Seq<i32>, i: int, j: int)
        requires 0 <= j <= i < nums.len(),
        ensures  Self::max_run(nums, i) >= Self::run_at(nums, j),
        decreases i,
    {
        if i > j {
            Self::lemma_max_run_ge(nums, i - 1, j);
        }
    }

    pub fn find_length_of_lcis(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 10_000,
            forall|i: int| 0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            1 <= res,
            res as int <= nums.len(),
            exists |start: int|
                0 <= start && start + res as int <= nums.len() as int &&
                #[trigger] Self::is_strictly_increasing(nums@, start, res as int),
            forall |start: int, len: int|
                0 <= start && 1 <= len && start + len <= nums.len() as int &&
                len > res as int ==>
                !#[trigger] Self::is_strictly_increasing(nums@, start, len),
    {
        let n = nums.len();
        let mut best: i32 = 1;
        let mut cur: i32 = 1;
        let mut i = 1usize;
        let ghost mut best_end: int = 0;

        while i < n
            invariant
                1 <= n <= 10_000,
                n == nums.len(),
                1 <= i <= n,
                forall|k: int| 0 <= k < nums.len() ==> -1_000_000_000 <= #[trigger] nums@[k] <= 1_000_000_000,
                cur as nat == Self::run_at(nums@, (i - 1) as int),
                best as nat == Self::max_run(nums@, (i - 1) as int),
                1 <= cur,
                1 <= best,
                0 <= best_end < i as int,
                Self::run_at(nums@, best_end) == best as nat,
            decreases n - i,
        {
            if nums[i] > nums[i - 1] {
                proof {
                    Self::lemma_run_at_bound(nums@, (i - 1) as int);
                    assert(cur < i32::MAX) by (nonlinear_arith)
                        requires cur as nat <= i as nat, i < n, n <= 10_000 {}
                }
                cur = cur + 1;
                if cur > best {
                    best = cur;
                    proof { best_end = i as int; }
                }
                proof {
                    assert(nums@[i as int] > nums@[i as int - 1]);
                    assert(Self::run_at(nums@, i as int)
                        == Self::run_at(nums@, i as int - 1) + 1);
                    assert(cur as nat == Self::run_at(nums@, i as int));
                    assert(Self::max_run(nums@, i as int)
                        == (if Self::run_at(nums@, i as int)
                               > Self::max_run(nums@, i as int - 1)
                            { Self::run_at(nums@, i as int) }
                            else { Self::max_run(nums@, i as int - 1) }));
                    assert(best as nat == Self::max_run(nums@, i as int));
                }
            } else {
                cur = 1;
                proof {
                    Self::lemma_run_at_pos(nums@, (i - 1) as int);
                    assert(Self::max_run(nums@, i as int)
                        == (if 1nat > Self::max_run(nums@, i as int - 1)
                            { 1nat }
                            else { Self::max_run(nums@, i as int - 1) }));
                    assert(best as nat == Self::max_run(nums@, i as int));
                }
            }
            i = i + 1;
        }

        proof {
            let end   = best_end;
            let start = end - best as int + 1;

            Self::lemma_run_at_increasing(nums@, end);
            Self::lemma_run_at_bound(nums@, end);
            assert(Self::is_strictly_increasing(nums@, end - best as int + 1, best as int));

            assert forall |s: int, len: int|
                0 <= s && 1 <= len && s + len <= n as int && len > best as int
                implies !Self::is_strictly_increasing(nums@, s, len) by
            {
                if Self::is_strictly_increasing(nums@, s, len) {
                    let end2 = s + len - 1;
                    Self::lemma_increasing_implies_run_at(nums@, s, s + len);
                    Self::lemma_max_run_ge(nums@, (n - 1) as int, end2);
                    assert(Self::max_run(nums@, (n - 1) as int) >= len as nat);
                    assert(Self::max_run(nums@, (n - 1) as int) == best as nat);
                    assert(false);
                }
            };
        }

        best
    }
}

} 
