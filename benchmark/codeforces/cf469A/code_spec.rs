use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn level_in_seq(seq: Seq<i32>, level: int) -> bool {
    exists|i: int| 0 <= i < seq.len() && #[trigger] seq[i] == level
}

pub open spec fn level_passable(level: int, x_levels: Seq<i32>, y_levels: Seq<i32>) -> bool {
    level_in_seq(x_levels, level) || level_in_seq(y_levels, level)
}

impl Solution {
    pub fn can_be_the_guy(n: i32, x_levels: Vec<i32>, y_levels: Vec<i32>) -> (res: bool)
        requires
            1 <= n <= 100,
            forall|i: int| 0 <= i < x_levels.len() ==> 1 <= #[trigger] x_levels[i] && x_levels[i] <= n,
            forall|i: int| 0 <= i < y_levels.len() ==> 1 <= #[trigger] y_levels[i] && y_levels[i] <= n,
        ensures
            res == (forall|k: int| 1 <= k && k <= (n as int) ==> #[trigger] level_passable(k, x_levels@, y_levels@)),
    {
        let mut k = 1i32;
        while k <= n {
            let x_len = x_levels.len();
            let y_len = y_levels.len();
            let mut found = false;
            let mut i = 0usize;
            while i < x_len && !found {
                if x_levels[i] == k {
                    found = true;
                } else {
                    i += 1;
                }
            }
            if !found {
                i = 0;
                while i < y_len && !found {
                    if y_levels[i] == k {
                        found = true;
                    } else {
                        i += 1;
                    }
                }
            }
            if !found {
                return false;
            }
            k += 1;
        }
        true
    }
}

}
