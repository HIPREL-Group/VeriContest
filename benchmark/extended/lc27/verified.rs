use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    
    pub open spec fn count_to(s: Seq<i32>, v: i32, end: int) -> int
        decreases end,
    {
        if end <= 0 { 0 }
        else { (if s[end - 1] == v { 1int } else { 0int }) + Self::count_to(s, v, end - 1) }
    }

    
    proof fn count_to_same_on_prefix(s1: Seq<i32>, s2: Seq<i32>, v: i32, end: int)
        requires
            end >= 0,
            s1.len() >= end,
            s2.len() >= end,
            forall |k: int| 0 <= k < end ==> s1[k] == s2[k],
        ensures
            Self::count_to(s1, v, end) == Self::count_to(s2, v, end),
        decreases end,
    {
        if end > 0 {
            Self::count_to_same_on_prefix(s1, s2, v, end - 1);
        }
    }

    pub fn remove_element(nums: &mut Vec<i32>, val: i32) -> (k: i32)
        requires
            0 <= old(nums).len() <= 100,
            forall |i: int| 0 <= i < old(nums).len() ==>
                0 <= #[trigger] old(nums)[i] <= 50,
            0 <= val <= 100,
        ensures
            0 <= k <= nums.len(),
            nums.len() == old(nums).len(),
            forall |i: int| 0 <= i < k as int ==> nums[i] != val,
            forall |v: i32| v != val ==>
                Self::count_to(nums@, v, k as int) ==
                    Self::count_to(old(nums)@, v, old(nums).len() as int),
    {
        let n = nums.len();
        let mut slow: usize = 0;
        let mut fast: usize = 0;

        while fast < n
            invariant
                n == nums.len(),
                nums.len() == old(nums).len(),
                0 <= n <= 100,
                0 <= slow <= fast <= n,
                0 <= val <= 100,
                forall |i: int| 0 <= i < old(nums).len() ==>
                    0 <= #[trigger] old(nums)[i] <= 50,
                forall |i: int| 0 <= i < slow as int ==> nums[i] != val,
                forall |i: int| fast as int <= i < n as int ==>
                    nums[i] == old(nums)[i],
                forall |v: i32| v != val ==>
                    Self::count_to(nums@, v, slow as int) ==
                        Self::count_to(old(nums)@, v, fast as int),
            decreases n - fast,
        {
            let ghost pre = nums@;
            let ghost old_slow = slow as int;

            if nums[fast] != val {
                let v = nums[fast];
                nums.set(slow, v);
                slow = slow + 1;

                proof {
                    assert(pre[fast as int] == old(nums)[fast as int]);
                    assert(v == old(nums)[fast as int]);
                    assert(v != val);
                    assert(nums@ =~= pre.update(old_slow, v));

                    assert forall |i: int| 0 <= i < slow as int
                        implies nums[i] != val by {
                        if i < old_slow {
                            assert(nums[i] == pre[i]);
                        } else {
                            assert(nums[i] == v);
                        }
                    };

                    assert forall |i: int| fast as int + 1 <= i < n as int
                        implies nums[i] == old(nums)[i] by {
                        assert(nums[i] == pre[i]);
                    };

                    assert forall |vv: i32| vv != val implies
                        Self::count_to(nums@, vv, slow as int) ==
                        Self::count_to(old(nums)@, vv, fast as int + 1) by {
                        Self::count_to_same_on_prefix(nums@, pre, vv, old_slow);
                    };
                }
            } else {
                proof {
                    assert(old(nums)[fast as int] == val);

                    assert forall |vv: i32| vv != val implies
                        Self::count_to(nums@, vv, slow as int) ==
                        Self::count_to(old(nums)@, vv, fast as int + 1) by {
                        
                    };
                }
            }
            fast = fast + 1;
        }

        slow as i32
    }
}

}
