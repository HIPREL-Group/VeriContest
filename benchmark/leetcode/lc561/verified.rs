use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {

    pub open spec fn even_index_sum(s: Seq<i32>) -> int
        decreases s.len()
    {
        if s.len() < 2 {
            0int
        } else {
            s[0] as int + Self::even_index_sum(s.subrange(2, s.len() as int))
        }
    }

    pub open spec fn sorted(s: Seq<i32>) -> bool {
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
    }

    pub fn array_pair_sum(nums: Vec<i32>) -> (result: i32)
        requires
            2 <= nums.len() <= 20000,
            nums.len() % 2 == 0,
            forall|i: int| 0 <= i < nums.len() ==> -10000 <= #[trigger] nums[i] <= 10000,
        ensures
            exists|sorted_nums: Seq<i32>|
                Self::sorted(sorted_nums)
                && sorted_nums.len() == nums.len()
                && result as int == Self::even_index_sum(sorted_nums),
    {
        let mut nums = nums;
        let n = nums.len();
        let mut i = 0usize;
        while i < n
            invariant
                i <= n,
                n == nums.len(),
                n <= 20000,
                n % 2 == 0,
                forall|k: int| 0 <= k < n ==> -10000 <= #[trigger] nums[k] <= 10000,
                forall|a: int, b: int| 0 <= a < b < i ==> nums@[a] <= nums@[b],
                forall|a: int, b: int| 0 <= a < i && i <= b < n ==> nums@[a] <= nums@[b],
            decreases n - i
        {
            let mut min_idx = i;
            let mut j = i + 1;
            while j < n
                invariant
                    i < n,
                    i <= min_idx < n,
                    i < j <= n,
                    n == nums.len(),
                    forall|k: int| 0 <= k < n ==> -10000 <= #[trigger] nums[k] <= 10000,
                    forall|k: int| i <= k < j ==> nums[min_idx as int] <= #[trigger] nums[k],
                decreases n - j
            {
                if nums[j] < nums[min_idx] {
                    min_idx = j;
                }
                j += 1;
            }

            let tmp = nums[i];
            nums[i] = nums[min_idx];
            nums[min_idx] = tmp;
            i += 1;
        }

        let mut sum: i32 = 0;
        let mut k = 0usize;
        let mut count: usize = 0;
        while k < n
            invariant
                k == count * 2,
                k <= n,
                n == nums.len(),
                n <= 20000,
                k % 2 == 0,
                n % 2 == 0,
                count <= 10000,
                forall|j: int| 0 <= j < n ==> -10000 <= #[trigger] nums[j] <= 10000,
                -(count as int) * 10000 <= sum <= (count as int) * 10000,
                sum as int == Self::even_index_sum(nums@.subrange(0, k as int)),
                Self::sorted(nums@),
            decreases n - k
        {
            assert(Self::even_index_sum(nums@.subrange(0, (k + 2) as int)) ==
                   nums@[k as int] as int + Self::even_index_sum(nums@.subrange(0, k as int))) by {
                Self::even_index_sum_extend_by_two(nums@, k as int);
            }
            sum = sum + nums[k];
            k += 2;
            count += 1;
        }
        
        sum
    }

    proof fn even_index_sum_extend_by_two(s: Seq<i32>, k: int)
        requires 0 <= k, k % 2 == 0, k + 2 <= s.len()
        ensures Self::even_index_sum(s.subrange(0, k + 2))
                == s[k] as int + Self::even_index_sum(s.subrange(0, k))
        decreases k
    {
        if k == 0 {
            let sub2 = s.subrange(0, 2);
            assert(sub2.len() == 2);
            assert(Self::even_index_sum(sub2) == sub2[0] as int + Self::even_index_sum(sub2.subrange(2, 2)));
            assert(sub2.subrange(2, 2).len() == 0);
            assert(Self::even_index_sum(sub2.subrange(2, 2)) == 0);
            assert(Self::even_index_sum(s.subrange(0, 0)) == 0) by {
                assert(s.subrange(0, 0).len() == 0);
            }
            assert(sub2[0] == s[0]) by { assert(sub2[0] == s.subrange(0, 2)[0]); }
        } else {
            let s2 = s.subrange(2, s.len() as int);
            assert(s2.len() == s.len() - 2);
            assert(s.subrange(2, k + 2) == s2.subrange(0, k));
            assert(s.subrange(2, k) == s2.subrange(0, k - 2));

            Self::even_index_sum_extend_by_two(s2, k - 2);

            let sk2 = s.subrange(0, k + 2);
            assert(Self::even_index_sum(sk2) == sk2[0] as int + Self::even_index_sum(sk2.subrange(2, sk2.len() as int)));
            assert(sk2.subrange(2, sk2.len() as int) == s.subrange(2, k + 2));

            let sk = s.subrange(0, k);
            assert(Self::even_index_sum(sk) == sk[0] as int + Self::even_index_sum(sk.subrange(2, sk.len() as int)));
            assert(sk.subrange(2, sk.len() as int) == s.subrange(2, k));
        }
    }
}
}

