use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn row_sum(row: Seq<i32>) -> int
        decreases row.len(),
    {
        if row.len() == 0 {
            0
        } else {
            row.last() as int + Self::row_sum(row.drop_last())
        }
    }

    pub fn maximum_wealth(accounts: Vec<Vec<i32>>) -> (result: i32)
        requires
            1 <= accounts.len() <= 50,
            1 <= accounts[0].len() <= 50,
            forall|i: int|
                0 <= i < accounts.len()
                    ==> #[trigger] accounts[i].len() == accounts[0].len(),
            forall|i: int, j: int|
                0 <= i < accounts.len() && 0 <= j < accounts[i].len()
                    ==> 1 <= #[trigger] accounts[i][j] <= 100,
        ensures
            exists|i: int| #![auto]
                0 <= i < accounts.len() && result as int == Self::row_sum(accounts@[i]@),
            forall|i: int| #![auto]
                0 <= i < accounts.len()
                    ==> result as int >= Self::row_sum(accounts@[i]@),
    {
        let mut max_wealth: i32 = 0;
        let mut i: usize = 0;
        while i < accounts.len() {
            let mut wealth: i32 = 0;
            let mut j: usize = 0;
            while j < accounts[i].len() {
                wealth += accounts[i][j];
                j += 1;
            }
            if wealth > max_wealth {
                max_wealth = wealth;
            }
            i += 1;
        }
        max_wealth
    }
}

} 
