use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn op_step(s: Seq<i32>, i: int) -> Seq<i32>
    {
        if 0 <= i + 1 < s.len() && s[i] == s[i + 1] {
            s.update(i, ((s[i] as int) * 2) as i32).update(i + 1, 0)
        } else {
            s
        }
    }

    pub open spec fn apply_ops_prefix(s: Seq<i32>, upto: int) -> Seq<i32>
        decreases upto,
    {
        if upto <= 0 || s.len() < 2 {
            s
        } else {
            let prev = Self::apply_ops_prefix(s, upto - 1);
            Self::op_step(prev, upto - 1)
        }
    }

    pub open spec fn nonzero_prefix(s: Seq<i32>, end: int) -> Seq<i32>
        decreases end,
    {
        if end <= 0 {
            seq![]
        } else if end > s.len() {
            Self::nonzero_prefix(s, s.len() as int)
        } else {
            let prev = Self::nonzero_prefix(s, end - 1);
            if s[end - 1] != 0 {
                prev.push(s[end - 1])
            } else {
                prev
            }
        }
    }

    pub open spec fn extend_with_zeros(base: Seq<i32>, total: int) -> Seq<i32>
        decreases total - base.len(),
    {
        if total <= base.len() {
            base
        } else {
            Self::extend_with_zeros(base, total - 1).push(0)
        }
    }

    pub open spec fn apply_operations_model(s: Seq<i32>) -> Seq<i32>
    {
        let transformed = Self::apply_ops_prefix(s, s.len() - 1);
        let nonz = Self::nonzero_prefix(transformed, transformed.len() as int);
        Self::extend_with_zeros(nonz, transformed.len() as int)
    }

    pub fn apply_operations(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            2 <= nums.len() <= 2000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1000,
        ensures
            result@ == Self::apply_operations_model(nums@),
    {
        let ghost orig = nums@;
        let mut nums = nums;
        let n = nums.len();

        let mut i: usize = 0;
        while i + 1 < n
            invariant
                2 <= n <= 2000,
                n == nums.len(),
                forall |k: int| 0 <= k < orig.len() ==> 0 <= #[trigger] orig[k] <= 1000,
                0 <= i <= n - 1,
                forall |k: int| 0 <= k < i ==> 0 <= #[trigger] nums[k] <= 2000,
                forall |k: int| i <= k < n ==> 0 <= #[trigger] nums[k] <= 1000,
                nums@ == Self::apply_ops_prefix(orig, i as int),
            decreases n - 1 - i,
        {
            let ghost before = nums@;

            if nums[i] == nums[i + 1] {
                proof {
                    assert(0 <= nums[i as int] <= 1000);
                    assert(-2147483648 <= nums[i as int] * 2 < 2147483648) by (nonlinear_arith)
                        requires
                            0 <= nums[i as int] <= 1000,
                    {
                    }
                }
                nums.set(i, nums[i] * 2);
                nums.set(i + 1, 0);
                proof {
                    assert(nums@ == before.update(i as int, ((before[i as int] as int) * 2) as i32).update(i as int + 1, 0));
                    assert(nums@ == Self::op_step(before, i as int));
                }
            } else {
                proof {
                    assert(nums@ == before);
                    assert(nums@ == Self::op_step(before, i as int));
                }
            }

            proof {
                assert(before == Self::apply_ops_prefix(orig, i as int));
                assert(Self::apply_ops_prefix(orig, i as int + 1)
                    == Self::op_step(Self::apply_ops_prefix(orig, i as int), i as int));
            }

            i = i + 1;
        }

        proof {
            assert(i as int + 1 >= n as int);
            assert(i as int <= n as int - 1);
            assert(i as int == n as int - 1);
        }

        let ghost transformed = nums@;

        proof {
            assert(transformed == Self::apply_ops_prefix(orig, n as int - 1));
        }

        let mut result: Vec<i32> = Vec::new();
        i = 0;
        while i < n
            invariant
                n == nums.len(),
                nums@ == transformed,
                0 <= i <= n,
                result.len() <= i,
                result@ == Self::nonzero_prefix(nums@, i as int),
            decreases n - i,
        {
            if nums[i] != 0 {
                result.push(nums[i]);
                proof {
                    assert(Self::nonzero_prefix(nums@, i as int + 1)
                        == Self::nonzero_prefix(nums@, i as int).push(nums[i as int]));
                }
            } else {
                proof {
                    assert(Self::nonzero_prefix(nums@, i as int + 1)
                        == Self::nonzero_prefix(nums@, i as int));
                }
            }
            i = i + 1;
        }

        let ghost nonz = result@;
        while result.len() < n
            invariant
                n == nums.len(),
                nums@ == transformed,
                nonz == Self::nonzero_prefix(nums@, n as int),
                nonz.len() <= result.len() as int,
                result.len() <= n,
                result@ == Self::extend_with_zeros(nonz, result.len() as int),
            decreases n - result.len(),
        {
            let old_len = result.len();
            let ghost before = result@;
            result.push(0);
            proof {
                assert(before == Self::extend_with_zeros(nonz, old_len as int));
                assert(result@ == before.push(0));
                assert(Self::extend_with_zeros(nonz, old_len as int + 1)
                    == Self::extend_with_zeros(nonz, old_len as int).push(0));
            }
        }

        proof {
            assert(n as int == orig.len());
            assert(nums@ == transformed);
            assert(transformed == Self::apply_ops_prefix(orig, n as int - 1));
            assert(result@ == Self::extend_with_zeros(Self::nonzero_prefix(transformed, n as int), n as int));
            assert(Self::apply_operations_model(orig)
                == Self::extend_with_zeros(
                    Self::nonzero_prefix(Self::apply_ops_prefix(orig, orig.len() as int - 1), orig.len() as int),
                    orig.len() as int,
                ));
            assert(result@ == Self::apply_operations_model(orig));
        }

        result
    }
}

}
