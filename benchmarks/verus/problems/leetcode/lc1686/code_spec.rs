use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_valid_play(play: Seq<usize>, n: int) -> bool {
        play.len() == n
        && (forall |i: int| 0 <= i < n ==> (#[trigger] play[i] as int) < n)
        && (forall |i: int, j: int| 0 <= i < j < n ==> play[i] != play[j])
    }

    pub open spec fn alice_score(play: Seq<usize>, av: Seq<i32>, k: int) -> int
        decreases k
    {
        if k <= 0 { 0 }
        else if (k - 1) % 2 == 0 {
            av[play[k - 1] as int] as int + Self::alice_score(play, av, k - 1)
        } else {
            Self::alice_score(play, av, k - 1)
        }
    }

    pub open spec fn bob_score(play: Seq<usize>, bv: Seq<i32>, k: int) -> int
        decreases k
    {
        if k <= 0 { 0 }
        else if (k - 1) % 2 == 1 {
            bv[play[k - 1] as int] as int + Self::bob_score(play, bv, k - 1)
        } else {
            Self::bob_score(play, bv, k - 1)
        }
    }

    pub open spec fn swap_gain(
        play: Seq<usize>, av: Seq<i32>, bv: Seq<i32>, k: int, j: int,
    ) -> int {
        let sk = play[k] as int;
        let sj = play[j] as int;
        (av[sj] as int + bv[sj] as int) - (av[sk] as int + bv[sk] as int)
    }

    pub open spec fn is_optimal_play(
        play: Seq<usize>, av: Seq<i32>, bv: Seq<i32>, n: int,
    ) -> bool {
        forall |k: int, j: int|
            0 <= k < j < n && k % 2 != j % 2
            ==> Self::swap_gain(play, av, bv, k, j) <= 0
    }

    pub fn stone_game_vi(alice_values: Vec<i32>, bob_values: Vec<i32>) -> (res: i32)
        requires
            alice_values.len() == bob_values.len(),
            1 <= alice_values.len() <= 100_000,
            forall |i: int| 0 <= i < alice_values.len() ==> 1 <= #[trigger] alice_values[i] <= 100,
            forall |i: int| 0 <= i < bob_values.len() ==> 1 <= #[trigger] bob_values[i] <= 100,
        ensures
            res == 1 || res == 0 || res == -1,
            exists |play: Seq<usize>|
                #[trigger] Self::is_valid_play(play, alice_values.len() as int)
                && Self::is_optimal_play(play, alice_values@, bob_values@, alice_values.len() as int)
                && {
                    let n = alice_values.len() as int;
                    let a_total = Self::alice_score(play, alice_values@, n);
                    let b_total = Self::bob_score(play, bob_values@, n);
                    (a_total > b_total ==> res == 1)
                    && (a_total < b_total ==> res == -1)
                    && (a_total == b_total ==> res == 0)
                },
    {
        let n = alice_values.len();
        let mut indices: Vec<usize> = Vec::new();
        let mut v: usize = 200;
        while v >= 2 {
            let mut i: usize = 0;
            while i < n {
                if alice_values[i] + bob_values[i] == v as i32 {
                    indices.push(i);
                }
                i += 1;
            }
            v -= 1;
        }
        let mut alice_total: i32 = 0;
        let mut bob_total: i32 = 0;
        let mut k: usize = 0;
        while k < n {
            if k % 2 == 0 {
                alice_total += alice_values[indices[k]];
            } else {
                bob_total += bob_values[indices[k]];
            }
            k += 1;
        }
        if alice_total > bob_total {
            1
        } else if alice_total < bob_total {
            -1
        } else {
            0
        }
    }
}

}
