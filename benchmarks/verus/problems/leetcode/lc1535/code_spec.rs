use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;




















impl Solution {
    pub open spec fn game_result(arr: Seq<i32>, k: int, pos: int, current: i32, wins: int) -> i32
        decreases arr.len() - pos,
    {
        if wins >= k {
            current
        } else if pos >= arr.len() {
            current
        } else if arr[pos] > current {
            Self::game_result(arr, k, pos + 1, arr[pos], 1)
        } else {
            Self::game_result(arr, k, pos + 1, current, wins + 1)
        }
    }

    pub fn get_winner(arr: Vec<i32>, k: i32) -> (result: i32)
        requires
            2 <= arr.len() <= 100_000,
            forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 1_000_000,
            forall |i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] != arr[j],
            1 <= k <= 1_000_000_000,
        ensures
            result == Self::game_result(arr@, k as int, 1, arr@[0], 0),
    {
        let mut current = arr[0];
        let mut wins: i32 = 0;
        let n = arr.len();
        let mut i: usize = 1;

        while i < n {
            if arr[i] > current {
                current = arr[i];
                wins = 1;
            } else {
                wins += 1;
            }

            if wins == k {
                return current;
            }

            i += 1;
        }

        current
    }
}

}
