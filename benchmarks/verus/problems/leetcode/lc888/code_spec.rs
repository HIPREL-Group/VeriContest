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

    pub open spec fn delta(alice_sizes: Seq<i32>, bob_sizes: Seq<i32>) -> int {
        (Self::seq_sum(alice_sizes, alice_sizes.len() as int) - Self::seq_sum(bob_sizes, bob_sizes.len() as int)) / 2
    }

    fn set_flag(flags: &mut Vec<bool>, idx: usize, value: bool)
        requires
            idx < old(flags)@.len(),
        ensures
            flags@.len() == old(flags)@.len(),
            forall |k: int| 0 <= k < flags@.len() ==> #[trigger] flags@[k] == if k == idx as int { value } else { old(flags)@[k] },
    {
        flags[idx] = value;
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
        let mut sum_a = 0i128;
        let mut i = 0usize;
        while i < alice_sizes.len()
        {
            sum_a = sum_a + alice_sizes[i] as i128;
            i = i + 1;
        }

        let mut sum_b = 0i128;
        i = 0usize;
        while i < bob_sizes.len()
        {
            sum_b = sum_b + bob_sizes[i] as i128;
            i = i + 1;
        }

        let delta = (sum_a - sum_b) / 2;

        let mut present: Vec<bool> = Vec::new();
        let mut size = 0usize;
        while size <= 100000usize
        {
            present.push(false);
            size = size + 1;
        }

        i = 0usize;
        while i < alice_sizes.len()
        {
            let idx = alice_sizes[i] as usize;
            Self::set_flag(&mut present, idx, true);
            i = i + 1;
        }

        let mut j = 0usize;
        while j < bob_sizes.len()
        {
            let target = bob_sizes[j] as i128 + delta as i128;
            if 1 <= target && target <= 100000 && present[target as usize] {
                let mut answer = Vec::new();
                answer.push(target as i32);
                answer.push(bob_sizes[j]);
                return answer;
            }
            j = j + 1;
        }

        Vec::new()
    }
}

}
