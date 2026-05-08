use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn seq_sum(s: Seq<i32>) -> int
        decreases s.len(),
    {
        if s.len() == 0 {
            0
        } else {
            Self::seq_sum(s.subrange(0, s.len() - 1)) + s[s.len() - 1] as int
        }
    }

    pub fn missing_rolls(rolls: Vec<i32>, mean: i32, n: i32) -> (res: Vec<i32>)
        requires
            1 <= rolls.len() <= 100_000,
            1 <= n <= 100_000,
            1 <= mean <= 6,
            forall |i: int| 0 <= i < rolls.len() ==> 1 <= #[trigger] rolls[i] <= 6,
        ensures
            (res@ =~= Seq::<i32>::empty()) == (
                mean as int * (rolls.len() as int + n as int) - Self::seq_sum(rolls@) < n as int
                || mean as int * (rolls.len() as int + n as int) - Self::seq_sum(rolls@) > 6 * n as int
            ),
            res@ != Seq::<i32>::empty() ==> (
                res.len() == n as int
                && (forall |i: int| 0 <= i < res.len() ==> 1 <= #[trigger] res[i] <= 6)
                && Self::seq_sum(res@)
                    == mean as int * (rolls.len() as int + n as int) - Self::seq_sum(rolls@)
            ),
    {
        let mut observed_sum = 0i128;
        let mut i: usize = 0;
        while i < rolls.len() {
            observed_sum += rolls[i] as i128;
            i += 1;
        }

        let missing_sum = mean as i128 * (rolls.len() as i128 + n as i128) - observed_sum;
        if missing_sum < n as i128 || missing_sum > 6 * n as i128 {
            return Vec::new();
        }

        let mut result: Vec<i32> = Vec::new();
        let mut remaining_sum = missing_sum;
        let mut remaining_slots = n as i128;
        while remaining_slots > 0 {
            let candidate = remaining_sum - 6 * (remaining_slots - 1);
            let val = if candidate > 1 { candidate } else { 1 };
            result.push(val as i32);
            remaining_sum -= val;
            remaining_slots -= 1;
        }

        result
    }
}

}
