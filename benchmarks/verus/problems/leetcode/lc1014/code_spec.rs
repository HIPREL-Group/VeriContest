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
        let second_left = values[1] + 1;
        if second_left > best_left {
            best_left = second_left;
        }
        let mut j = 2usize;
        while j < n {
            let candidate = best_left + values[j] - j as i32;
            if candidate > best {
                best = candidate;
            }
            let left_candidate = values[j] + j as i32;
            if left_candidate > best_left {
                best_left = left_candidate;
            }
            j += 1;
        }
        best
    }
}

}
