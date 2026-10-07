use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn rotated_index(i: int, k: int, n: int) -> int
        recommends n > 0
    {
        (n - k % n + i) % n
    }

    fn reverse_range(nums: &mut Vec<i32>, l: usize, r: usize)
        requires
            l <= r,
            r < old(nums).len(),
        ensures
            nums.len() == old(nums).len(),
            forall |j: int| 0 <= j < nums.len() && !(l as int <= j <= r as int) ==> nums[j] == old(nums)[j],
            forall |j: int| l as int <= j <= r as int ==> nums[j] == old(nums)[l as int + r as int - j],
    {
        let ghost orig = nums@;
        let mut lo = l;
        let mut hi = r;
        while lo < hi
            invariant
                l <= lo,
                hi <= r,
                lo as int + hi as int == l as int + r as int,
                nums.len() == old(nums).len(),
                r < nums.len(),
                orig == old(nums)@,
                forall |j: int| l as int <= j && j < lo as int ==> nums[j] == orig[l as int + r as int - j],
                forall |j: int| hi as int + 1 <= j && j <= r as int ==> nums[j] == orig[l as int + r as int - j],
                forall |j: int| lo as int <= j && j <= hi as int ==> nums[j] == orig[j],
                forall |j: int| 0 <= j < nums.len() && !(l as int <= j && j <= r as int) ==> nums[j] == orig[j],
            decreases hi as int + 1 - lo as int,
        {
            let tmp = nums[lo];
            nums[lo] = nums[hi];
            nums[hi] = tmp;
            lo = lo + 1;
            hi = hi - 1;
        }
    }

    pub fn rotate(nums: &mut Vec<i32>, k: i32)
        requires
            1 <= old(nums).len() <= 100_000,
            0 <= k <= 100_000,
        ensures
            nums.len() == old(nums).len(),
            forall |i: int| 0 <= i < nums.len() ==> nums[i] == old(nums)[Self::rotated_index(i, k as int, nums.len() as int)],
    {
        let n = nums.len();
        let kk = (k as usize) % n;

        if kk == 0 {
            proof {
                assert forall |j: int| 0 <= j < nums.len() implies
                    nums[j] == old(nums)[Self::rotated_index(j, k as int, nums.len() as int)] by {
                    assert((n as int + j) % n as int == j) by (nonlinear_arith)
                        requires n as int > 0, 0 <= j < n as int;
                };
            }
            return;
        }

        let ghost orig = nums@;

        Self::reverse_range(nums, 0, n - 1);
        let ghost after1 = nums@;

        Self::reverse_range(nums, 0, kk - 1);
        let ghost after2 = nums@;

        Self::reverse_range(nums, kk, n - 1);

        proof {
            assert(orig =~= old(nums)@);
            assert forall |j: int| 0 <= j < n as int implies
                nums[j] == old(nums)[Self::rotated_index(j, k as int, n as int)] by {
                if j < kk as int {
                    
                    
                    
                    assert(nums@[j] == after2[j]);
                    assert(after2[j] == after1[kk as int - 1 - j]);
                    assert(after1[kk as int - 1 - j] == orig[n as int - kk as int + j]);
                    
                    assert(Self::rotated_index(j, k as int, n as int) == n as int - kk as int + j) by {
                        assert((n as int - kk as int + j) % n as int == n as int - kk as int + j)
                            by (nonlinear_arith)
                            requires 0 < kk as int, j < kk as int, 0 <= j,
                                     0 < n as int, kk as int <= n as int;
                    };
                } else {
                    
                    
                    
                    let idx: int = kk as int + n as int - 1 - j;
                    assert(0 <= idx < n as int);
                    assert(idx >= kk as int);
                    assert(nums@[j] == after2[idx]);
                    assert(after2[idx] == after1[idx]);
                    assert(after1[idx] == orig[j - kk as int]);
                    
                    assert(Self::rotated_index(j, k as int, n as int) == j - kk as int) by {
                        assert((n as int - kk as int + j) % n as int == j - kk as int)
                            by (nonlinear_arith)
                            requires 0 < kk as int, kk as int <= j, j < n as int, 0 < n as int;
                    };
                }
            };
        }
    }
}

} 
