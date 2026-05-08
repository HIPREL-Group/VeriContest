use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_first_mult(l: int, k: int) -> int {
    (l + k - 1) / k * k
}

pub open spec fn feasible(n: int, l: int, r: int) -> bool {
    forall|j: int|
        #![trigger spec_first_mult(l, j + 1)]
        0 <= j && j < n ==> spec_first_mult(l, j + 1) <= r && spec_first_mult(l, j + 1) >= l
}

pub open spec fn seq_matches_witness(n: int, l: int, r: int, s: Seq<i32>) -> bool {
    s.len() == n
        && (forall|i: int|
            0 <= i && i < n ==> s[i] == spec_first_mult(l, i + 1))
}

impl Solution {
    #[verifier::exec_allows_no_decreases_clause]
    pub fn construct_gcd_array(n: usize, l: i32, r: i32) -> (res: (bool, Vec<i32>))
        requires
            1 <= n <= 100_000,
            1 <= l <= r <= 1_000_000_000,
        ensures
            res.0 == feasible(n as int, l as int, r as int),
            !res.0 ==> res.1.len() == 0,
            res.0 ==> res.1.len() == n,
            res.0 ==> seq_matches_witness(n as int, l as int, r as int, res.1@),
            res.0 ==> (forall|i: int|
                0 <= i && i < n ==> l as int <= #[trigger] res.1@[i] && res.1@[i] <= r as int),
            res.0 ==> (forall|i: int|
                0 <= i && i < n ==> 1 <= #[trigger] res.1@[i]),
    {
        let mut a: Vec<i32> = Vec::new();
        let mut t: usize = 0;
        while t < n {
            a.push(0i32);
            t = t + 1;
        }
        let mut i: usize = 0;
        while i < n {
            let k = (i + 1) as i32;
            let k64 = k as i64;
            let num: i64 = l as i64 + k64 - 1;
            let q = num / k64;
            let first = (q * k64) as i32;
            if first > r {
                return (false, Vec::new());
            }
            a.set(i, first);
            i = i + 1;
        }
        (true, a)
    }
}

}
