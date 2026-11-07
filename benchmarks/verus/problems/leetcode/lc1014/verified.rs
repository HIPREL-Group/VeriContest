use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn pair_score(values: Seq<i32>, i: int, j: int) -> int
        recommends
            0 <= i < j < values.len(),
    {
        values[i] as int + values[j] as int + i - j
    }

    pub fn max_score_sightseeing_pair(values: Vec<i32>) -> (result: i32)
        requires
            2 <= values.len() <= 50_000,
            forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1000,
        ensures
            exists|i: int, j: int|
                0 <= i < j < values.len() && result as int == Self::pair_score(values@, i, j),
            forall|i: int, j: int|
                0 <= i < j < values.len() ==> Self::pair_score(values@, i, j) <= result as int,
    {
        let n = values.len();
        let mut best_left = values[0];
        let mut best = values[0] + values[1] - 1;
        let ghost mut best_left_idx: int = 0;
        let ghost mut best_i: int = 0;
        let ghost mut best_j: int = 1;
        let second_left = values[1] + 1;
        if second_left > best_left {
            proof {
                best_left_idx = 1;
            }
            best_left = second_left;
        }
        
        let mut j = 2usize;
        while j < n
            invariant
                n == values.len(),
                2 <= n <= 50_000,
                2 <= j <= n,
                forall|k: int| 0 <= k < n ==> 1 <= #[trigger] values[k] <= 1000,
                0 <= best_left_idx < j as int,
                best_left as int == values@[best_left_idx] as int + best_left_idx,
                forall|i: int| 0 <= i < j as int ==> values[i] as int + i <= best_left as int,
                0 <= best_i < best_j < j as int,
                best as int == Self::pair_score(values@, best_i, best_j),
                forall|i: int, k: int| 0 <= i < k < j as int ==> Self::pair_score(values@, i, k) <= best as int,
            decreases n - j,
        {
            let ghost old_j: int = j as int;
            let ghost old_best: int = best as int;

            let candidate = best_left + values[j] - j as i32;
            if candidate > best {
                proof {
                    best_i = best_left_idx;
                    best_j = old_j;
                }
                best = candidate;
            }

            let left_candidate = values[j] + j as i32;
            if left_candidate > best_left {
                proof {
                    best_left_idx = old_j;
                }
                best_left = left_candidate;
            }

            j += 1;
        }
        best
    }
}

}
