use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn common_divisor(cnt: Seq<i32>, d: int) -> bool
        recommends
            cnt.len() == 30,
    {
        &&& 1 <= d
        &&& forall|b: int| 0 <= b < 30 ==> #[trigger] ((cnt[b] as int) % d) == 0
    }

    pub open spec fn valid_answer(n: int, cnt: Seq<i32>, ans: Seq<i32>) -> bool
        recommends
            cnt.len() == 30,
            n >= 1,
    {
        &&& forall|idx: int| 0 <= idx < ans.len() ==> 1 <= ans[idx] as int <= n && Self::common_divisor(cnt, ans[idx] as int)
        &&& forall|d: int| 1 <= d <= n && Self::common_divisor(cnt, d) ==> exists|idx: int| 0 <= idx < ans.len() && ans[idx] as int == d
    }

    pub fn valid_k_values(n: usize, cnt: Vec<i32>) -> (ans: Vec<i32>)
        requires
            1 <= n <= 200_000,
            cnt.len() == 30,
            forall|i: int| 0 <= i < 30 ==> 0 <= #[trigger] cnt[i] <= n,
        ensures
            Self::valid_answer(n as int, cnt@, ans@),
    {
        let mut ans: Vec<i32> = Vec::new();
        let mut k: usize = 1;

        while k <= n {
            let k_i32: i32 = k as i32;
            let mut b: usize = 0;
            let mut bad_idx: i32 = -1;

            while b < 30 {
                if bad_idx == -1 && cnt[b] % k_i32 != 0 {
                    bad_idx = b as i32;
                }
                b = b + 1;
            }

            if bad_idx == -1 {
                ans.push(k as i32);
            }

            k = k + 1;
        }

        ans
    }
}

}
