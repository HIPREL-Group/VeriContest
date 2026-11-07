use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_non_decreasing(s: Seq<i32>) -> bool {
        forall|i: int| 0 <= i < s.len() as int - 1 ==> #[trigger] s[i] <= s[i + 1]
    }

    pub open spec fn can_fix_with_one_change(nums: Seq<i32>) -> bool {
        Self::is_non_decreasing(nums)
        || exists|k: int, v: i32|
            0 <= k < nums.len() as int
            && Self::is_non_decreasing(#[trigger] nums.update(k, v))
    }

    pub open spec fn can_fix_at_index(nums: Seq<i32>, k: int) -> bool {
        &&& 0 <= k < nums.len() as int
        &&& forall|j: int|
                0 <= j < nums.len() as int - 1 ==>
                (j == k - 1 || j == k || #[trigger] nums[j] <= nums[j + 1])
        &&& (0 < k && k < nums.len() as int - 1 ==> nums[k - 1] <= nums[k + 1])
    }

    proof fn lemma_can_fix_at_index_implies_exists_update(nums: Seq<i32>, k: int)
        requires
            1 <= nums.len(),
            Self::can_fix_at_index(nums, k),
        ensures
            exists|v: i32| Self::is_non_decreasing(#[trigger] nums.update(k, v)),
    {
        let n = nums.len() as int;
        let v: i32 = if n == 1 {
            nums[0]
        } else if k == 0 {
            nums[1]
        } else {
            nums[k - 1]
        };

        assert(Self::is_non_decreasing(nums.update(k, v))) by {
            assert forall|j: int| 0 <= j < n - 1 implies #[trigger] nums.update(k, v)[j] <= nums.update(k, v)[j + 1] by {
                if j == k - 1 {
                    assert(nums.update(k, v)[j] == nums[j]);
                    assert(nums.update(k, v)[j + 1] == v);
                    assert(v == nums[k - 1]);
                } else if j == k {
                    if k == 0 {
                        assert(nums.update(k, v)[0] == v);
                        assert(nums.update(k, v)[1] == nums[1]);
                    } else if k < n - 1 {
                        assert(nums.update(k, v)[k] == v);
                        assert(nums.update(k, v)[k + 1] == nums[k + 1]);
                    }
                } else {
                    assert(nums.update(k, v)[j] == nums[j]);
                    assert(nums.update(k, v)[j + 1] == nums[j + 1]);
                    assert(nums[j] <= nums[j + 1]);
                }
            }
        };
    }

    proof fn lemma_exists_update_implies_can_fix_at_index(nums: Seq<i32>, k: int, v: i32)
        requires
            1 <= nums.len(),
            0 <= k < nums.len() as int,
            Self::is_non_decreasing(nums.update(k, v)),
        ensures
            Self::can_fix_at_index(nums, k),
    {
        let n = nums.len() as int;
        assert(Self::can_fix_at_index(nums, k)) by {
            assert forall|j: int|
                0 <= j < n - 1 implies
                    (j == k - 1 || j == k || #[trigger] nums[j] <= nums[j + 1]) by {
                if j != k - 1 && j != k {
                    assert(nums.update(k, v)[j] == nums[j]);
                    assert(nums.update(k, v)[j + 1] == nums[j + 1]);
                    assert(nums[j] <= nums[j + 1]);
                }
            }
            if 0 < k && k < n - 1 {
                assert(nums.update(k, v)[k - 1] <= nums.update(k, v)[k]);
                assert(nums.update(k, v)[k] <= nums.update(k, v)[k + 1]);
                assert(nums.update(k, v)[k - 1] == nums[k - 1]);
                assert(nums.update(k, v)[k + 1] == nums[k + 1]);
            }
        }
    }

    proof fn lemma_can_fix_equiv_exists_index(nums: Seq<i32>)
        requires
            1 <= nums.len(),
        ensures
            Self::can_fix_with_one_change(nums) <==>
            exists|k: int| 0 <= k < nums.len() as int && Self::can_fix_at_index(nums, k),
    {
        let n = nums.len() as int;
        assert(Self::can_fix_with_one_change(nums) ==> exists|k: int| 0 <= k < n && Self::can_fix_at_index(nums, k)) by {
            if Self::can_fix_with_one_change(nums) {
                if Self::is_non_decreasing(nums) {
                    assert(Self::can_fix_at_index(nums, 0)) by {
                        assert forall|j: int|
                            0 <= j < n - 1 implies
                            (j == -1 || j == 0 || #[trigger] nums[j] <= nums[j + 1]) by {
                            assert(nums[j] <= nums[j + 1]);
                        }
                    };
                } else {
                    let kv = choose|k: int, v: i32|
                        0 <= k < n && Self::is_non_decreasing(nums.update(k, v));
                    let k = kv.0;
                    let v = kv.1;
                    assert(Self::is_non_decreasing(nums.update(k, v)));
                    Self::lemma_exists_update_implies_can_fix_at_index(nums, k, v);
                }
            }
        };

        assert((exists|k: int| 0 <= k < n && Self::can_fix_at_index(nums, k)) ==> Self::can_fix_with_one_change(nums)) by {
            if exists|k: int| 0 <= k < n && Self::can_fix_at_index(nums, k) {
                let k = choose|k: int| 0 <= k < n && Self::can_fix_at_index(nums, k);
                Self::lemma_can_fix_at_index_implies_exists_update(nums, k);
                let v = choose|v: i32| Self::is_non_decreasing(nums.update(k, v));
                assert(Self::is_non_decreasing(nums.update(k, v)));
                assert(Self::can_fix_with_one_change(nums));
            }
        };
    }

    fn check_index(nums: &Vec<i32>, k: usize) -> (ok: bool)
        requires
            1 <= nums.len(),
            k < nums.len(),
        ensures
            ok <==> Self::can_fix_at_index(nums@, k as int),
    {
        let n = nums.len();
        let mut j = 0usize;

        while j + 1 < n
            invariant
                n == nums.len(),
                k < n,
                0 <= j < n,
                forall|t: int| 0 <= t < j as int ==>
                    (t == k as int - 1 || t == k as int
                        || (t + 1 < n as int && #[trigger] nums@[t] <= nums@[t + 1])),
            decreases n - j,
        {
            if nums[j] > nums[j + 1] && !(j + 1 == k || j == k) {
                proof {
                    assert(!Self::can_fix_at_index(nums@, k as int)) by {
                        assert(!(j as int == k as int - 1 || j as int == k as int || nums@[j as int] <= nums@[j as int + 1]));
                    }
                }
                return false;
            }
            j += 1;
        }

        if 0 < k && k + 1 < n && nums[k - 1] > nums[k + 1] {
            return false;
        }

        proof {
            assert(Self::can_fix_at_index(nums@, k as int)) by {
                assert(forall|t: int| 0 <= t && t + 1 < n as int ==>
                    (t == k as int - 1 || t == k as int || #[trigger] nums@[t] <= nums@[t + 1]));
                if 0 < k as int && k as int + 1 < n as int {
                    assert(nums@[k as int - 1] <= nums@[k as int + 1]);
                }
            }
        }
        true
    }

    pub fn check_possibility(nums: Vec<i32>) -> (result: bool)
        requires
            1 <= nums.len() <= 10_000,
            forall|i: int| 0 <= i < nums.len() ==> -100_000 <= #[trigger] nums[i] <= 100_000,
        ensures
            result <==> Self::can_fix_with_one_change(nums@),
    {
        let n = nums.len();
        let mut k = 0usize;

        while k < n
            invariant
                n == nums.len(),
                1 <= n <= 10_000,
                0 <= k <= n,
                forall|t: int| 0 <= t < k as int ==> !Self::can_fix_at_index(nums@, t),
            decreases n - k,
        {
            let ok = Self::check_index(&nums, k);
            if ok {
                proof {
                    assert(Self::can_fix_at_index(nums@, k as int));
                    Self::lemma_can_fix_at_index_implies_exists_update(nums@, k as int);
                    let v = choose|v: i32| Self::is_non_decreasing(nums@.update(k as int, v));
                    assert(Self::is_non_decreasing(nums@.update(k as int, v)));
                    assert(Self::can_fix_with_one_change(nums@));
                }
                return true;
            }
            proof {
                assert(!Self::can_fix_at_index(nums@, k as int));
            }
            k += 1;
        }

        proof {
            Self::lemma_can_fix_equiv_exists_index(nums@);
            assert(!Self::can_fix_with_one_change(nums@)) by {
                if Self::can_fix_with_one_change(nums@) {
                    let w = choose|t: int| 0 <= t < n as int && Self::can_fix_at_index(nums@, t);
                    assert(0 <= w < n as int);
                    assert(Self::can_fix_at_index(nums@, w));
                    assert(!Self::can_fix_at_index(nums@, w));
                }
            }
        }
        false
    }
}

} 
