use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sum_to(chalk: Seq<i32>, i: int) -> int
        decreases i,
    {
        if i <= 0 {
            0
        } else {
            Self::sum_to(chalk, i - 1) + chalk[i - 1] as int
        }
    }

    pub fn chalk_replacer(chalk: Vec<i32>, k: i32) -> (res: i32)
        requires
            1 <= chalk.len() <= 100_000,
            forall |i: int| 0 <= i < chalk.len() ==> 1 <= #[trigger] chalk[i] <= 100_000,
            1 <= k <= 1_000_000_000,
        ensures
            0 <= res < chalk.len(),
            Self::sum_to(chalk@, res as int) <= k as int % Self::sum_to(chalk@, chalk.len() as int),
            k as int % Self::sum_to(chalk@, chalk.len() as int) < Self::sum_to(chalk@, res as int + 1),
    {
        let n = chalk.len();
        let mut total: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            total = total + chalk[i] as i64;
            i += 1;
        }
        let mut remainder: i64 = k as i64 % total;
        let mut j: usize = 0;
        while j < n {
            if remainder < chalk[j] as i64 {
                return j as i32;
            }
            remainder = remainder - chalk[j] as i64;
            j += 1;
        }
        0
    }
}

}
