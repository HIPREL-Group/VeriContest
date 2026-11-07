use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn seq_sum(s: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::seq_sum(s, end - 1) + s[end - 1] as int
        }
    }

    pub open spec fn appears_in(s: Seq<i32>, value: i32) -> bool {
        exists |i: int| 0 <= i < s.len() && #[trigger] s[i] == value
    }

    pub open spec fn valid_swap_int(alice_sizes: Seq<i32>, bob_sizes: Seq<i32>, alice_box: int, bob_box: int) -> bool {
        &&& 1 <= alice_box <= 100_000
        &&& 1 <= bob_box <= 100_000
        &&& Self::appears_in(alice_sizes, alice_box as i32)
        &&& Self::appears_in(bob_sizes, bob_box as i32)
        &&& Self::seq_sum(alice_sizes, alice_sizes.len() as int) - alice_box + bob_box
            == Self::seq_sum(bob_sizes, bob_sizes.len() as int) - bob_box + alice_box
    }

    pub open spec fn valid_swap(alice_sizes: Seq<i32>, bob_sizes: Seq<i32>, alice_box: i32, bob_box: i32) -> bool {
        Self::valid_swap_int(alice_sizes, bob_sizes, alice_box as int, bob_box as int)
    }

    pub fn fair_candy_swap(alice_sizes: Vec<i32>, bob_sizes: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= alice_sizes.len() <= 10_000,
            1 <= bob_sizes.len() <= 10_000,
            forall |i: int| 0 <= i < alice_sizes.len() ==> 1 <= #[trigger] alice_sizes[i] <= 100_000,
            forall |j: int| 0 <= j < bob_sizes.len() ==> 1 <= #[trigger] bob_sizes[j] <= 100_000,
            Self::seq_sum(alice_sizes@, alice_sizes.len() as int) != Self::seq_sum(bob_sizes@, bob_sizes.len() as int),
            exists |alice_box: int, bob_box: int| Self::valid_swap_int(alice_sizes@, bob_sizes@, alice_box, bob_box),
        ensures
            result.len() == 2,
            Self::valid_swap(alice_sizes@, bob_sizes@, result[0], result[1]),
    {
    }
}

}
