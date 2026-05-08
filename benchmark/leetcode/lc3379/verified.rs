use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn step_right(pos: int, n: int) -> int
        recommends
            n > 0,
            0 <= pos < n,
    {
        if pos + 1 < n { pos + 1 } else { 0 }
    }

    pub open spec fn step_left(pos: int, n: int) -> int
        recommends
            n > 0,
            0 <= pos < n,
    {
        if pos > 0 { pos - 1 } else { n - 1 }
    }

    pub open spec fn move_right(pos: int, steps: nat, n: int) -> int
        recommends
            n > 0,
            0 <= pos < n,
        decreases steps,
    {
        if steps == 0 {
            pos
        } else {
            Self::step_right(Self::move_right(pos, (steps - 1) as nat, n), n)
        }
    }

    pub open spec fn move_left(pos: int, steps: nat, n: int) -> int
        recommends
            n > 0,
            0 <= pos < n,
        decreases steps,
    {
        if steps == 0 {
            pos
        } else {
            Self::step_left(Self::move_left(pos, (steps - 1) as nat, n), n)
        }
    }

    pub open spec fn transformed_index(nums: Seq<i32>, i: int) -> int
        recommends
            nums.len() > 0,
            0 <= i < nums.len(),
    {
        let delta = nums[i] as int;
        if delta >= 0 {
            Self::move_right(i, delta as nat, nums.len() as int)
        } else {
            Self::move_left(i, (-delta) as nat, nums.len() as int)
        }
    }

    proof fn lemma_step_right_in_range(pos: int, n: int)
        requires
            n > 0,
            0 <= pos < n,
        ensures
            0 <= Self::step_right(pos, n) < n,
    {
    }

    proof fn lemma_step_left_in_range(pos: int, n: int)
        requires
            n > 0,
            0 <= pos < n,
        ensures
            0 <= Self::step_left(pos, n) < n,
    {
    }

    proof fn lemma_move_right_in_range(pos: int, steps: nat, n: int)
        requires
            n > 0,
            0 <= pos < n,
        ensures
            0 <= Self::move_right(pos, steps, n) < n,
        decreases steps,
    {
        if steps > 0 {
            Self::lemma_move_right_in_range(pos, (steps - 1) as nat, n);
            Self::lemma_step_right_in_range(Self::move_right(pos, (steps - 1) as nat, n), n);
        }
    }

    proof fn lemma_move_left_in_range(pos: int, steps: nat, n: int)
        requires
            n > 0,
            0 <= pos < n,
        ensures
            0 <= Self::move_left(pos, steps, n) < n,
        decreases steps,
    {
        if steps > 0 {
            Self::lemma_move_left_in_range(pos, (steps - 1) as nat, n);
            Self::lemma_step_left_in_range(Self::move_left(pos, (steps - 1) as nat, n), n);
        }
    }

    pub fn construct_transformed_array(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> -100 <= #[trigger] nums[i] <= 100,
        ensures
            result.len() == nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> #[trigger] result[i] == nums[Self::transformed_index(nums@, i)],
    {
        let n = nums.len();
        let mut result = vec![0i32; n];
        let mut i: usize = 0;
        while i < n
            invariant
                n == nums.len(),
                1 <= n <= 100,
                result.len() == n,
                0 <= i <= n,
                forall |k: int| 0 <= k < nums.len() ==> -100 <= #[trigger] nums[k] <= 100,
                forall |k: int| 0 <= k < i as int ==> #[trigger] result[k] == nums[Self::transformed_index(nums@, k)],
            decreases n - i,
        {
            let delta: i32 = nums[i];
            if delta == 0 {
                result.set(i, nums[i]);
                proof {
                    assert(delta as int == nums@[i as int] as int);
                    assert(Self::move_right(i as int, 0nat, n as int) == i as int);
                    assert(Self::transformed_index(nums@, i as int) == i as int);
                    assert(result[i as int] == nums[Self::transformed_index(nums@, i as int)]);
                }
            } else if delta > 0 {
                let mut pos: usize = i;
                let mut step: i32 = 0;
                while step < delta
                    invariant
                        n == nums.len(),
                        1 <= n <= 100,
                        0 <= i < n,
                        delta == nums[i as int],
                        0 < delta <= 100,
                        0 <= step <= delta,
                        0 <= pos < n,
                        pos as int == Self::move_right(i as int, step as nat, n as int),
                    decreases delta - step,
                {
                    let old_pos = pos;
                    let old_step = step;
                    if pos + 1 < n {
                        pos = pos + 1;
                    } else {
                        pos = 0;
                    }
                    step = step + 1;
                    proof {
                        if old_pos + 1 < n {
                            assert(Self::step_right(old_pos as int, n as int) == old_pos as int + 1);
                            assert(pos as int == Self::step_right(old_pos as int, n as int));
                        } else {
                            assert(Self::step_right(old_pos as int, n as int) == 0);
                            assert(pos as int == Self::step_right(old_pos as int, n as int));
                        }
                        assert(old_step + 1 == step);
                        assert(old_step >= 0);
                        assert(step > 0);
                        assert(old_pos as int == Self::move_right(i as int, old_step as nat, n as int));
                        assert(Self::move_right(i as int, step as nat, n as int)
                            == Self::step_right(Self::move_right(i as int, (step - 1) as nat, n as int), n as int));
                        assert((step - 1) as nat == old_step as nat);
                        assert(Self::move_right(i as int, step as nat, n as int)
                            == Self::step_right(Self::move_right(i as int, old_step as nat, n as int), n as int));
                        assert(pos as int == Self::move_right(i as int, step as nat, n as int));
                    }
                }
                result.set(i, nums[pos]);
                proof {
                    assert(step == delta);
                    assert(pos as int == Self::move_right(i as int, delta as nat, n as int));
                    assert(delta as int == nums@[i as int] as int);
                    assert(Self::transformed_index(nums@, i as int)
                        == Self::move_right(i as int, delta as nat, n as int));
                    assert(Self::transformed_index(nums@, i as int) == pos as int);
                    assert(result[i as int] == nums[Self::transformed_index(nums@, i as int)]);
                }
            } else {
                let mut pos: usize = i;
                let mut step: i32 = 0;
                let target: i32 = -delta;
                while step < target
                    invariant
                        n == nums.len(),
                        1 <= n <= 100,
                        0 <= i < n,
                        delta == nums[i as int],
                        -100 <= delta < 0,
                        0 < target <= 100,
                        target == -delta,
                        0 <= step <= target,
                        0 <= pos < n,
                        pos as int == Self::move_left(i as int, step as nat, n as int),
                    decreases target - step,
                {
                    let old_pos = pos;
                    let old_step = step;
                    if pos > 0 {
                        pos = pos - 1;
                    } else {
                        pos = n - 1;
                    }
                    step = step + 1;
                    proof {
                        if old_pos > 0 {
                            assert(Self::step_left(old_pos as int, n as int) == old_pos as int - 1);
                            assert(pos as int == Self::step_left(old_pos as int, n as int));
                        } else {
                            assert(Self::step_left(old_pos as int, n as int) == n as int - 1);
                            assert(pos as int == Self::step_left(old_pos as int, n as int));
                        }
                        assert(old_step + 1 == step);
                        assert(old_step >= 0);
                        assert(step > 0);
                        assert(old_pos as int == Self::move_left(i as int, old_step as nat, n as int));
                        assert(Self::move_left(i as int, step as nat, n as int)
                            == Self::step_left(Self::move_left(i as int, (step - 1) as nat, n as int), n as int));
                        assert((step - 1) as nat == old_step as nat);
                        assert(Self::move_left(i as int, step as nat, n as int)
                            == Self::step_left(Self::move_left(i as int, old_step as nat, n as int), n as int));
                        assert(pos as int == Self::move_left(i as int, step as nat, n as int));
                    }
                }
                result.set(i, nums[pos]);
                proof {
                    assert(step == target);
                    assert(pos as int == Self::move_left(i as int, target as nat, n as int));
                    assert(target == -delta);
                    assert(delta as int == nums@[i as int] as int);
                    assert(Self::transformed_index(nums@, i as int)
                        == Self::move_left(i as int, (-nums@[i as int] as int) as nat, n as int));
                    assert((-nums@[i as int] as int) as nat == target as nat);
                    assert(Self::transformed_index(nums@, i as int)
                        == Self::move_left(i as int, target as nat, n as int));
                    assert(Self::transformed_index(nums@, i as int) == pos as int);
                    assert(result[i as int] == nums[Self::transformed_index(nums@, i as int)]);
                }
            }
            proof {
                assert forall |k: int| 0 <= k < (i + 1) as int implies #[trigger] result[k] == nums[Self::transformed_index(nums@, k)] by {
                    if k == i as int {
                    } else {
                        assert(0 <= k < i as int);
                    }
                }
            }
            i = i + 1;
        }
        result
    }
}

}
