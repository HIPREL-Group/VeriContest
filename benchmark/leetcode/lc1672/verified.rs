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
        let ghost mut best_idx: int = 0;
        let mut i: usize = 0;
        while i < accounts.len()
            invariant
                0 <= i <= accounts.len(),
                1 <= accounts.len() <= 50,
                1 <= accounts[0].len() <= 50,
                forall|k: int|
                    0 <= k < accounts.len()
                        ==> #[trigger] accounts[k].len() == accounts[0].len(),
                forall|k: int, l: int|
                    0 <= k < accounts.len() && 0 <= l < accounts[k].len()
                        ==> 1 <= #[trigger] accounts[k][l] <= 100,
                i == 0 ==> max_wealth == 0,
                i > 0 ==> 0 <= best_idx < i as int,
                i > 0 ==> max_wealth as int == Self::row_sum(accounts@[best_idx]@),
                forall|k: int| #![auto]
                    0 <= k < i as int
                        ==> max_wealth as int >= Self::row_sum(accounts@[k]@),
                0 <= max_wealth <= 5000,
            decreases accounts.len() - i,
        {
            let mut wealth: i32 = 0;
            let mut j: usize = 0;
            while j < accounts[i].len()
                invariant
                    0 <= i < accounts.len(),
                    0 <= j <= accounts[i as int].len(),
                    1 <= accounts[i as int].len() <= 50,
                    forall|l: int|
                        0 <= l < accounts[i as int].len()
                            ==> 1 <= #[trigger] accounts[i as int][l] <= 100,
                    wealth as int == Self::row_sum(accounts@[i as int]@.subrange(0, j as int)),
                    j as int <= wealth as int <= j as int * 100,
                decreases accounts[i as int].len() - j,
            {
                proof {
                    let sub = accounts@[i as int]@.subrange(0, (j + 1) as int);
                    assert(sub.last() == accounts@[i as int]@[j as int]);
                    assert(sub.drop_last() =~= accounts@[i as int]@.subrange(0, j as int));
                }
                wealth += accounts[i][j];
                j += 1;
            }
            proof {
                assert(accounts@[i as int]@.subrange(0, accounts@[i as int]@.len() as int)
                    =~= accounts@[i as int]@);
                assert(wealth as int >= accounts@[i as int]@.len());
                assert(wealth >= 1);
            }
            if wealth > max_wealth {
                max_wealth = wealth;
                proof {
                    best_idx = i as int;
                }
            }
            i += 1;
        }
        max_wealth
    }
}

} 
