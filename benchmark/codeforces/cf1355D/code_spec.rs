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

    pub open spec fn block_sum(nums: Seq<i64>, lo: int, hi: int) -> int
        recommends
            0 <= lo <= hi <= nums.len(),
    {
        Self::prefix_sum(nums, hi) - Self::prefix_sum(nums, lo)
    }

    pub open spec fn petya_wins(a: Seq<i64>, n: int, s: int, k: int) -> bool {
        &&& a.len() == n
        &&& Self::total_sum(a) == s
        &&& forall|i: int| 0 <= i < n ==> #[trigger] a[i] as int >= 1
        &&& 0 <= k <= s
        &&& forall|lo: int, hi: int|
            0 <= lo < hi <= n ==> #[trigger] Self::block_sum(a, lo, hi) != k
                && Self::block_sum(a, lo, hi) != s - k
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn construct_game(n: i64, s: i64) -> (result: Option<(Vec<i64>, i64)>)
        requires
            1 <= n <= s <= 1_000_000,
        ensures
            result == None::<(Vec<i64>, i64)> <==> (s as int) < 2 * (n as int),
            result != None::<(Vec<i64>, i64)> ==> {
                let p = result->Some_0;
                &&& p.0.len() == n as usize
                &&& p.1 == n
                &&& Self::petya_wins(p.0@, n as int, s as int, p.1 as int)
            },
    {
        if s < 2 * n {
            return None;
        }
        let nu = n as usize;
        let mut a: Vec<i64> = Vec::new();
        let mut i = 0usize;
        while i < nu - 1 {
            a.push(1i64);
            i = i + 1;
        }
        a.push(s - (n - 1));
        Some((a, n))
    }
}

}
