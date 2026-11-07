use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn fraction_less(s: Seq<i32>, a: int, b: int, num_idx: int, den_idx: int) -> bool {
        (s[a] as int) * (s[den_idx] as int) < (s[num_idx] as int) * (s[b] as int)
    }

    pub open spec fn count_less_inner(s: Seq<i32>, num_idx: int, den_idx: int, a: int, b: int) -> nat
        decreases (s.len() - b) as nat
    {
        if b >= s.len() {
            0nat
        } else if a >= b {
            0nat
        } else {
            let add = if Self::fraction_less(s, a, b, num_idx, den_idx) { 1nat } else { 0nat };
            add + Self::count_less_inner(s, num_idx, den_idx, a, b + 1)
        }
    }

    pub open spec fn count_less_outer(s: Seq<i32>, num_idx: int, den_idx: int, a: int) -> nat
        decreases (s.len() - a) as nat
    {
        if a >= s.len() {
            0nat
        } else {
            Self::count_less_inner(s, num_idx, den_idx, a, a + 1)
                + Self::count_less_outer(s, num_idx, den_idx, a + 1)
        }
    }

    pub open spec fn count_fractions_less(s: Seq<i32>, num_idx: int, den_idx: int) -> nat {
        Self::count_less_outer(s, num_idx, den_idx, 0)
    }

    pub open spec fn is_prime(n: int) -> bool {
        n >= 2 && forall|d: int| 2 <= d < n ==> #[trigger](n % d) != 0
    }

    #[verifier::loop_isolation(false)]
    pub fn kth_smallest_prime_fraction(arr: Vec<i32>, k: i32) -> (result: Vec<i32>)
        requires
            2 <= arr.len() <= 1000,
            forall|i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 30_000,
            arr[0] == 1,
            forall|i: int| 1 <= i < arr.len() ==> #[trigger] Self::is_prime(arr[i] as int),
            forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] < arr[j],
            1 <= k <= (arr.len() * (arr.len() - 1) / 2) as int,
            exists|i: int, j: int|
                0 <= i < j < arr.len()
                && #[trigger] Self::count_fractions_less(arr@, i, j) == (k - 1) as nat,
        ensures
            result.len() == 2,
            exists|i: int, j: int|
                0 <= i < j < arr.len()
                && #[trigger] result@[0] == arr@[i]
                && result@[1] == arr@[j]
                && Self::count_fractions_less(arr@, i, j) == (k - 1) as nat,
    {
        let n = arr.len();
        let scale: i64 = 1i64 << 32;
        let mut lo: i64 = 0;
        let mut hi: i64 = scale;
        let mut ans_i: usize = 0;
        let mut ans_j: usize = 1;

        let mut iter: u32 = 0;
        while iter < 32 {
            let mid: i64 = lo + (hi - lo) / 2;
            let mut count: i32 = 0;
            let mut best_i: usize = 0;
            let mut best_j: usize = 1;
            let mut found: bool = false;
            let mut i: usize = 0;
            let mut j: usize = 1;
            while j < n {
                i = 0;
                while i < j && (arr[i] as i64) * scale <= mid * (arr[j] as i64) {
                    let take = if !found {
                        true
                    } else {
                        (arr[i] as i64) * (arr[best_j] as i64) >= (arr[best_i] as i64) * (arr[j] as i64)
                    };
                    if take {
                        best_i = i;
                        best_j = j;
                        found = true;
                    }
                    i += 1;
                }
                count = count + (i as i32);
                j += 1;
            }

            if count < k {
                lo = mid;
            } else {
                hi = mid;
                ans_i = best_i;
                ans_j = best_j;
            }
            iter += 1;
        }

        let mut result = Vec::new();
        result.push(arr[ans_i]);
        result.push(arr[ans_j]);
        result
    }
}

}
