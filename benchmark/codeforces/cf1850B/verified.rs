use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_valid(a: Seq<u32>, idx: int) -> bool {
    0 <= idx < a.len() && a[idx] <= 10
}

impl Solution {
    pub fn find_winner(a: Vec<u32>, b: Vec<u32>, n: usize) -> (result: usize)
        requires
            1 <= n <= 50,
            a.len() == n,
            b.len() == n,
            forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 50,
            forall|i: int| 0 <= i < b.len() ==> 1 <= #[trigger] b[i] <= 50,
            exists|i: int| 0 <= i < a.len() && #[trigger] a[i] <= 10,
        ensures
            1 <= result <= n,
            a[result as int - 1] <= 10,
            forall|j: int| 0 <= j < n && #[trigger] a[j] <= 10 ==> b[j] <= b[result as int - 1],
    {
        let mut best_idx: usize = 0;
        let mut best_b: u32 = 0;
        let mut found: bool = false;
        let mut i: usize = 0;
        while i < n
            invariant
                1 <= n <= 50,
                a.len() == n,
                b.len() == n,
                forall|k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= 50,
                forall|k: int| 0 <= k < b.len() ==> 1 <= #[trigger] b[k] <= 50,
                0 <= i <= n,
                found ==> (best_idx < n && a[best_idx as int] <= 10 && best_b == b[best_idx as int]),
                forall|j: int| 0 <= j < i && #[trigger] a[j] <= 10 ==> found && b[j] <= best_b,
            decreases n - i,
        {
            if a[i] <= 10 {
                if !found || b[i] > best_b {
                    best_idx = i;
                    best_b = b[i];
                    found = true;
                }
            }
            i += 1;
        }
        proof {
            assert(found) by {
                assert(exists|k: int| 0 <= k < a.len() && #[trigger] a[k] <= 10);
                let witness = choose|k: int| 0 <= k < a.len() && #[trigger] a[k] <= 10;
                assert(0 <= witness < n && a[witness] <= 10);
            }
        }
        best_idx + 1
    }
}

}
