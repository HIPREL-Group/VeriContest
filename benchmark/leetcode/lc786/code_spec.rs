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
        let mut ptr: Vec<usize> = Vec::with_capacity(n);
        let mut idx: usize = 0;
        while idx < n {
            ptr.push(0);
            idx += 1;
        }

        let mut ans_i: usize = 0;
        let mut ans_j: usize = 1;

        let mut t: i32 = 0;
        while t < k {
            let mut best_j: usize = 0;
            let mut j: usize = 1;
            while j < n {
                if ptr[j] < j {
                    let take = if best_j == 0 {
                        true
                    } else {
                        (arr[ptr[j]] as i64) * (arr[best_j] as i64) < (arr[ptr[best_j]] as i64) * (arr[j] as i64)
                    };
                    if take {
                        best_j = j;
                    }
                }
                j += 1;
            }

            ans_i = ptr[best_j];
            ans_j = best_j;
            ptr[best_j] = ptr[best_j] + 1;

            t += 1;
        }

        let mut result = Vec::new();
        result.push(arr[ans_i]);
        result.push(arr[ans_j]);
        result
    }
}

}
