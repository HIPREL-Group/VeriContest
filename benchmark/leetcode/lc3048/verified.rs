use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn last_pos(change_indices: Seq<i32>, idx: int, t: int) -> int
        recommends
            0 <= idx,
            0 <= t <= change_indices.len(),
        decreases t,
    {
        if t <= 0 {
            -1
        } else {
            if change_indices[t - 1] as int == idx + 1 {
                t - 1
            } else {
                Self::last_pos(change_indices, idx, t - 1)
            }
        }
    }

    pub open spec fn scan_state(nums: Seq<i32>, change_indices: Seq<i32>, t: int, s: int) -> int
        recommends
            0 <= s <= t <= change_indices.len(),
            forall|i: int| 0 <= i < t ==> 1 <= #[trigger] change_indices[i] <= nums.len(),
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i],
        decreases s,
    {
        if s <= 0 {
            0
        } else {
            let prev = Self::scan_state(nums, change_indices, t, s - 1);
            if prev < 0 {
                -1
            } else {
                let idx = change_indices[s - 1] as int - 1;
                if s - 1 == Self::last_pos(change_indices, idx, t) {
                    if prev < nums[idx] as int {
                        -1
                    } else {
                        prev - nums[idx] as int
                    }
                } else {
                    prev + 1
                }
            }
        }
    }

    pub open spec fn can_mark_spec(nums: Seq<i32>, change_indices: Seq<i32>, t: int) -> bool
        recommends
            0 <= t <= change_indices.len(),
            forall|i: int| 0 <= i < t ==> 1 <= #[trigger] change_indices[i] <= nums.len(),
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i],
    {
        (forall|idx: int| 0 <= idx < nums.len() ==> #[trigger] Self::last_pos(change_indices, idx, t) >= 0)
            && Self::scan_state(nums, change_indices, t, t) >= 0
    }

    proof fn lemma_last_pos_ge_minus_one(change_indices: Seq<i32>, idx: int, t: int)
        requires
            0 <= idx,
            0 <= t <= change_indices.len(),
        ensures
            Self::last_pos(change_indices, idx, t) >= -1,
        decreases t,
    {
        if t > 0 {
            if change_indices[t - 1] as int != idx + 1 {
                Self::lemma_last_pos_ge_minus_one(change_indices, idx, t - 1);
            }
        }
    }

    proof fn lemma_scan_state_stays_negative(nums: Seq<i32>, change_indices: Seq<i32>, t: int, s1: int, s2: int)
        requires
            0 <= s1 <= s2 <= t <= change_indices.len(),
            forall|i: int| 0 <= i < t ==> 1 <= #[trigger] change_indices[i] <= nums.len(),
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i],
            Self::scan_state(nums, change_indices, t, s1) < 0,
        ensures
            Self::scan_state(nums, change_indices, t, s2) < 0,
        decreases s2 - s1,
    {
        if s1 < s2 {
            Self::lemma_scan_state_stays_negative(nums, change_indices, t, s1, s2 - 1);
            assert(Self::scan_state(nums, change_indices, t, s2) == -1);
        }
    }

    fn can_mark(nums: &Vec<i32>, change_indices: &Vec<i32>, t: usize) -> (res: bool)
        requires
            1 <= nums.len() <= 2000,
            1 <= change_indices.len() <= 2000,
            1 <= t <= change_indices.len(),
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000_000,
            forall|i: int| 0 <= i < change_indices.len() ==> 1 <= #[trigger] change_indices[i] <= nums.len(),
        ensures
            res == Self::can_mark_spec(nums@, change_indices@, t as int),
    {
        let n = nums.len();
        let mut last: Vec<i32> = vec![-1; n];

        let mut i: usize = 0;
        while i < t
            invariant
                n == nums.len(),
                1 <= nums.len() <= 2000,
                1 <= change_indices.len() <= 2000,
                1 <= t <= change_indices.len(),
                0 <= i <= t,
                last.len() == n,
                forall|k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] <= 1_000_000_000,
                forall|k: int| 0 <= k < change_indices.len() ==> 1 <= #[trigger] change_indices[k] <= nums.len(),
                forall|j: int| 0 <= j < n ==> -1 <= #[trigger] last[j],
                forall|j: int| 0 <= j < n ==> #[trigger] last[j] as int == Self::last_pos(change_indices@, j, i as int),
            decreases t - i,
        {
            let idx = (change_indices[i] - 1) as usize;
            proof {
                assert(0 <= idx < n);
                assert(change_indices[i as int] as int == idx as int + 1);
            }
            let ghost last_before = last@;
            proof {
                assert forall|j: int| 0 <= j < n implies last_before[j] as int == Self::last_pos(change_indices@, j, i as int) by {
                    assert(last_before[j] == last@[j]);
                }
            }
            last.set(idx, i as i32);
            proof {
                assert(last@ == last_before.update(idx as int, i as i32));
                assert forall|j: int| 0 <= j < n implies #[trigger] last[j] as int == Self::last_pos(change_indices@, j, (i + 1) as int) by {
                    if j == idx as int {
                        assert(change_indices[i as int] as int == j + 1);
                        assert(Self::last_pos(change_indices@, j, (i + 1) as int) == i as int);
                        assert(last[j] == i as i32);
                    } else {
                        assert(change_indices[i as int] as int != j + 1);
                        assert(Self::last_pos(change_indices@, j, (i + 1) as int) == Self::last_pos(change_indices@, j, i as int));
                        assert(last[j] == last_before[j]);
                        assert(last_before[j] as int == Self::last_pos(change_indices@, j, i as int));
                    }
                }
            }
            i += 1;
        }

        i = 0;
        while i < n
            invariant
                n == nums.len(),
                1 <= nums.len() <= 2000,
                1 <= change_indices.len() <= 2000,
                1 <= t <= change_indices.len(),
                last.len() == n,
                0 <= i <= n,
                forall|k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] <= 1_000_000_000,
                forall|k: int| 0 <= k < change_indices.len() ==> 1 <= #[trigger] change_indices[k] <= nums.len(),
                forall|j: int| 0 <= j < n ==> -1 <= #[trigger] last[j],
                forall|j: int| 0 <= j < n ==> #[trigger] last[j] as int == Self::last_pos(change_indices@, j, t as int),
                forall|j: int| 0 <= j < i ==> last[j] >= 0,
            decreases n - i,
        {
            let cur = last[i];
            if cur == -1 {
                proof {
                    assert(Self::last_pos(change_indices@, i as int, t as int) < 0);
                    assert(!(forall|idx: int| 0 <= idx < nums.len() ==> #[trigger] Self::last_pos(change_indices@, idx, t as int) >= 0)) by {
                        let idx = i as int;
                        assert(0 <= idx < nums.len());
                        assert(Self::last_pos(change_indices@, idx, t as int) < 0);
                    }
                    assert(!Self::can_mark_spec(nums@, change_indices@, t as int));
                }
                return false;
            }
            proof {
                assert(cur != -1);
                let curi = cur as int;
                assert(curi >= -1);
                if curi < 0 {
                    assert(curi == -1) by (nonlinear_arith)
                        requires
                            curi >= -1,
                            curi < 0,
                    {}
                    assert(cur == -1);
                    assert(false);
                }
                assert(curi >= 0);
                assert(last[i as int] == cur);
                assert(last[i as int] as int == curi);
                assert(last[i as int] as int >= 0);
            }
            i += 1;
        }

        let mut slots: i64 = 0;
        i = 0;
        while i < t
            invariant
                n == nums.len(),
                1 <= nums.len() <= 2000,
                1 <= change_indices.len() <= 2000,
                1 <= t <= change_indices.len(),
                0 <= i <= t,
                last.len() == n,
                forall|k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] <= 1_000_000_000,
                forall|k: int| 0 <= k < change_indices.len() ==> 1 <= #[trigger] change_indices[k] <= nums.len(),
                forall|j: int| 0 <= j < n ==> -1 <= #[trigger] last[j],
                forall|j: int| 0 <= j < n ==> #[trigger] last[j] as int == Self::last_pos(change_indices@, j, t as int),
                forall|j: int| 0 <= j < n ==> last[j] >= 0,
                slots as int == Self::scan_state(nums@, change_indices@, t as int, i as int),
                0 <= slots as int <= i as int,
            decreases t - i,
        {
            let idx = (change_indices[i] - 1) as usize;
            proof {
                assert(0 <= idx < n);
                assert(change_indices[i as int] as int == idx as int + 1);
            }
            if last[idx] == i as i32 {
                let old_slots = slots;
                proof {
                    assert(Self::last_pos(change_indices@, idx as int, t as int) == i as int);
                }
                if old_slots < nums[idx] as i64 {
                    proof {
                        assert(Self::scan_state(nums@, change_indices@, t as int, i as int) == old_slots as int);
                        assert(Self::scan_state(nums@, change_indices@, t as int, (i + 1) as int) == -1);
                        Self::lemma_scan_state_stays_negative(nums@, change_indices@, t as int, (i + 1) as int, t as int);
                        assert(!Self::can_mark_spec(nums@, change_indices@, t as int));
                    }
                    return false;
                }
                slots -= nums[idx] as i64;
                proof {
                    assert(Self::scan_state(nums@, change_indices@, t as int, (i + 1) as int) == old_slots as int - nums[idx as int] as int);
                    assert(old_slots as int >= nums[idx as int] as int);
                    assert(slots as int == old_slots as int - nums[idx as int] as int);
                    assert(slots as int == Self::scan_state(nums@, change_indices@, t as int, (i + 1) as int));
                    assert(0 <= slots as int);
                    assert(slots as int <= i as int);
                }
            } else {
                let old_slots = slots;
                proof {
                    assert(old_slots as int <= i as int);
                    assert(old_slots <= 2000);
                    assert(old_slots + 1 <= 9_223_372_036_854_775_807);
                }
                slots += 1;
                proof {
                    assert(Self::last_pos(change_indices@, idx as int, t as int) != i as int);
                    assert(Self::scan_state(nums@, change_indices@, t as int, (i + 1) as int) == old_slots as int + 1);
                    assert(slots as int == old_slots as int + 1);
                    assert(slots as int == Self::scan_state(nums@, change_indices@, t as int, (i + 1) as int));
                    assert(0 <= slots as int <= (i + 1) as int);
                }
            }
            i += 1;
        }

        proof {
            assert forall|idx: int| 0 <= idx < nums.len() implies #[trigger] Self::last_pos(change_indices@, idx, t as int) >= 0 by {
                assert(last[idx] >= 0);
                assert(Self::last_pos(change_indices@, idx, t as int) == last[idx] as int);
            }
            assert(Self::scan_state(nums@, change_indices@, t as int, t as int) >= 0);
            assert(Self::can_mark_spec(nums@, change_indices@, t as int));
        }

        true
    }

    pub fn earliest_second_to_mark_indices(nums: Vec<i32>, change_indices: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 2000,
            1 <= change_indices.len() <= 2000,
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000_000,
            forall|i: int| 0 <= i < change_indices.len() ==> 1 <= #[trigger] change_indices[i] <= nums.len(),
        ensures
            res == -1 ==> forall|t: int| 1 <= t <= change_indices.len() ==> !#[trigger] Self::can_mark_spec(nums@, change_indices@, t),
            res != -1 ==> (
                1 <= res <= change_indices.len()
                && Self::can_mark_spec(nums@, change_indices@, res as int)
                && forall|t: int| 1 <= t < res ==> !#[trigger] Self::can_mark_spec(nums@, change_indices@, t)
            ),
    {
        let m = change_indices.len();
        let mut t: usize = 1;
        while t <= m
            invariant
                m == change_indices.len(),
                1 <= nums.len() <= 2000,
                1 <= m <= 2000,
                1 <= t <= m + 1,
                forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000_000,
                forall|i: int| 0 <= i < change_indices.len() ==> 1 <= #[trigger] change_indices[i] <= nums.len(),
                forall|k: int| 1 <= k < t as int ==> !#[trigger] Self::can_mark_spec(nums@, change_indices@, k),
            decreases m + 1 - t,
        {
            if Self::can_mark(&nums, &change_indices, t) {
                proof {
                    assert(Self::can_mark_spec(nums@, change_indices@, t as int));
                }
                return t as i32;
            }
            proof {
                assert(!Self::can_mark_spec(nums@, change_indices@, t as int));
            }
            t += 1;
        }
        proof {
            assert(t == m + 1);
            assert forall|k: int| 1 <= k <= m as int implies !#[trigger] Self::can_mark_spec(nums@, change_indices@, k) by {
            }
        }
        -1
    }
}

}
