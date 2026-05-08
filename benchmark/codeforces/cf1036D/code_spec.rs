use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn prefix_sum(nums: Seq<i64>, end: int) -> int
        recommends
            0 <= end <= nums.len(),
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::prefix_sum(nums, end - 1) + nums[end - 1] as int
        }
    }

    pub open spec fn total_sum(nums: Seq<i64>) -> int {
        Self::prefix_sum(nums, nums.len() as int)
    }

    pub open spec fn block_sum(nums: Seq<i64>, lo: int, hi: int) -> int {
        Self::prefix_sum(nums, hi) - Self::prefix_sum(nums, lo)
    }

    pub open spec fn valid_equal_partition(
        a: Seq<i64>, na: int, b: Seq<i64>, nb: int,
        k: int, pa: Seq<int>, pb: Seq<int>,
    ) -> bool {
        &&& k >= 1
        &&& pa.len() == k + 1
        &&& pb.len() == k + 1
        &&& pa[0] == 0
        &&& pa[k] == na
        &&& pb[0] == 0
        &&& pb[k] == nb
        &&& forall|i: int| 0 <= i < k ==> pa[i] < #[trigger] pa[i + 1]
        &&& forall|i: int| 0 <= i < k ==> pb[i] < #[trigger] pb[i + 1]
        &&& forall|i: int| 0 <= i < k ==>
                Self::block_sum(a, pa[i], #[trigger] pa[i + 1])
                == Self::block_sum(b, pb[i], pb[i + 1])
    }

    pub fn max_equal_block_count(a: Vec<i64>, b: Vec<i64>) -> (result: i64)
        requires
            1 <= a.len() <= 300_000,
            1 <= b.len() <= 300_000,
            forall|x: int| 0 <= x < a.len() ==> 1 <= #[trigger] a[x] as int && (a[x] as int) <= 1_000_000_000,
            forall|x: int| 0 <= x < b.len() ==> 1 <= #[trigger] b[x] as int && (b[x] as int) <= 1_000_000_000,
            Self::total_sum(a@) <= i64::MAX,
            Self::total_sum(b@) <= i64::MAX,
        ensures
            (result == -1) == (Self::total_sum(a@) != Self::total_sum(b@)),
            result >= 0 ==> result >= 1,
            result >= 0 ==> exists|pa: Seq<int>, pb: Seq<int>|
                Self::valid_equal_partition(a@, a.len() as int, b@, b.len() as int, result as int, pa, pb),
    {
        let n = a.len();
        let m = b.len();
        let mut ta: i64 = 0;
        let mut tb: i64 = 0;
        let mut u = 0usize;
        while u < n {
            ta = ta + a[u];
            u = u + 1;
        }
        u = 0usize;
        while u < m {
            tb = tb + b[u];
            u = u + 1;
        }
        if ta != tb {
            return -1;
        }
        let mut i = 0usize;
        let mut j = 0usize;
        let mut sa: i64 = 0;
        let mut sb: i64 = 0;
        let mut ans: i64 = 0;
        while i < n || j < m {
            if sa <= sb {
                if i < n {
                    sa = sa + a[i];
                    i = i + 1;
                } else {
                    sb = sb + b[j];
                    j = j + 1;
                }
            } else {
                if j < m {
                    sb = sb + b[j];
                    j = j + 1;
                } else {
                    sa = sa + a[i];
                    i = i + 1;
                }
            }
            if sa == sb && sa > 0 {
                ans = ans + 1;
                sa = 0;
                sb = 0;
            }
        }
        ans
    }
}

}
