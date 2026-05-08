use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_prime(n: int) -> bool {
        n == 2 || n == 3 || n == 5 || n == 7 || n == 11 || n == 13 || n == 17 || n == 19
            || n == 23 || n == 29 || n == 31 || n == 37 || n == 41 || n == 43 || n == 47
            || n == 53 || n == 59 || n == 61 || n == 67 || n == 71 || n == 73 || n == 79
            || n == 83 || n == 89 || n == 97
    }

    pub fn is_prime_exec(n: i32) -> (result: bool)
        ensures
            result == Self::is_prime(n as int),
    {
        n == 2 || n == 3 || n == 5 || n == 7 || n == 11 || n == 13 || n == 17 || n == 19
            || n == 23 || n == 29 || n == 31 || n == 37 || n == 41 || n == 43 || n == 47
            || n == 53 || n == 59 || n == 61 || n == 67 || n == 71 || n == 73 || n == 79
            || n == 83 || n == 89 || n == 97
    }

    pub fn maximum_prime_difference(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 300000,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
            exists|i: int| 0 <= i < nums.len() && Self::is_prime(nums[i] as int),
        ensures
            result >= 0,
            exists|i: int, j: int|
                0 <= i <= j < nums.len()
                && Self::is_prime(nums[i] as int)
                && Self::is_prime(nums[j] as int)
                && #[trigger] (j - i) == result,
            forall|i: int, j: int|
                0 <= i <= j < nums.len()
                && Self::is_prime(nums[i] as int)
                && Self::is_prime(nums[j] as int)
                ==> #[trigger] (j - i) <= result,
    {
        let n = nums.len();
        let mut first: usize = 0;
        let mut last: usize = 0;
        let mut found = false;
        let mut idx: usize = 0;

        while idx < n
            invariant
                1 <= n <= 300000,
                n == nums.len(),
                0 <= idx <= n,
                forall|k: int| 0 <= k < n as int ==> 1 <= #[trigger] nums[k] <= 100,
                !found ==> forall|k: int| 0 <= k < idx as int ==> !Self::is_prime(#[trigger] nums[k] as int),
                found ==> 0 <= first <= last < idx <= n,
                found ==> Self::is_prime(nums[first as int] as int),
                found ==> Self::is_prime(nums[last as int] as int),
                found ==> forall|k: int| 0 <= k < first as int ==> !Self::is_prime(#[trigger] nums[k] as int),
                found ==> forall|k: int| 0 <= k < idx as int ==> (k <= last as int || !Self::is_prime(#[trigger] nums[k] as int)),
            decreases n - idx,
        {
            if Self::is_prime_exec(nums[idx]) {
                if !found {
                    first = idx;
                    last = idx;
                    found = true;
                } else {
                    last = idx;
                }
            }
            idx = idx + 1;
        }

        assert(found) by {
            if !found {
                let witness = choose|i: int| 0 <= i < nums.len() && Self::is_prime(nums[i] as int);
                assert(0 <= witness < nums.len());
                assert(idx == n);
                assert(!Self::is_prime(nums[witness] as int));
                assert(Self::is_prime(nums[witness] as int));
            }
        };

        let mut result: i32 = 0;
        let mut t: usize = first;
        while t < last
            invariant
                1 <= n <= 300000,
                n == nums.len(),
                found,
                0 <= first <= last < n,
                Self::is_prime(nums[first as int] as int),
                Self::is_prime(nums[last as int] as int),
                forall|k: int| 0 <= k < first as int ==> !Self::is_prime(#[trigger] nums[k] as int),
                forall|k: int| 0 <= k < n as int ==> (k <= last as int || !Self::is_prime(#[trigger] nums[k] as int)),
                first <= t <= last,
                result >= 0,
                result as int == t as int - first as int,
                result as int <= 300000,
            decreases last - t,
        {
            t = t + 1;
            result = result + 1;
        }

        proof {
            assert(t == last);
            assert(result as int == last as int - first as int);

            assert(exists|i: int, j: int|
                0 <= i <= j < nums.len()
                    && Self::is_prime(nums[i] as int)
                    && Self::is_prime(nums[j] as int)
                    && (j - i) == result) by {
                let i = first as int;
                let j = last as int;
                assert(0 <= i <= j < nums.len());
                assert(Self::is_prime(nums[i] as int));
                assert(Self::is_prime(nums[j] as int));
                assert(j - i == result as int);
            };

            assert forall|i: int, j: int|
                0 <= i <= j < nums.len()
                    && Self::is_prime(nums[i] as int)
                    && Self::is_prime(nums[j] as int)
                    implies (j - i) <= result by {
                if 0 <= i <= j < nums.len()
                    && Self::is_prime(nums[i] as int)
                    && Self::is_prime(nums[j] as int) {
                    assert(first as int <= i) by {
                        if i < first as int {
                            assert(!Self::is_prime(nums[i] as int));
                            assert(Self::is_prime(nums[i] as int));
                        }
                    };
                    assert(j <= last as int) by {
                        if j > last as int {
                            assert(!(j <= last as int));
                            assert(j < n as int);
                            assert(j <= last as int || !Self::is_prime(nums[j] as int));
                            assert(!Self::is_prime(nums[j] as int));
                            assert(Self::is_prime(nums[j] as int));
                        }
                    };
                    assert(j - i <= last as int - first as int);
                    assert(last as int - first as int == result as int);
                }
            };
        }

        result
    }
}

}
