use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn in_circular_range(s: int, start: int, end: int, n: int) -> bool {
        if start <= end {
            start <= s && s <= end
        } else {
            (1 <= s && s <= end) || (start <= s && s <= n)
        }
    }

    pub fn most_visited(n: i32, rounds: Vec<i32>) -> (result: Vec<i32>)
        requires
            2 <= n <= 100,
            rounds.len() >= 2,
            rounds.len() <= 101,
            forall |i: int| 0 <= i < rounds.len() ==> 1 <= #[trigger] rounds[i] <= n,
            forall |i: int| 0 <= i < rounds.len() - 1 ==> (#[trigger] rounds[i]) != rounds[i + 1],
        ensures
            result@.len() >= 1,
            forall |i: int| 0 <= i < result@.len() ==> 1 <= #[trigger] result@[i] <= n,
            forall |i: int, j: int| 0 <= i < j < result@.len() ==> result@[i] < result@[j],
            forall |i: int| 0 <= i < result@.len() ==>
                Self::in_circular_range(
                    (#[trigger] result@[i]) as int,
                    rounds[0] as int,
                    rounds[rounds.len() - 1] as int,
                    n as int,
                ),
            forall |s: int| 1 <= s <= n as int && (#[trigger] Self::in_circular_range(
                s,
                rounds[0] as int,
                rounds[rounds.len() - 1] as int,
                n as int,
            )) ==> exists |i: int| 0 <= i < result@.len() && result@[i] as int == s,
    {
        let start = rounds[0];
        let end_val = rounds[rounds.len() - 1];
        let mut result: Vec<i32> = Vec::new();
        if start <= end_val {
            let mut s = start;
            while s <= end_val {
                result.push(s);
                s = s + 1;
            }
        } else {
            let mut s: i32 = 1;
            while s <= end_val {
                result.push(s);
                s = s + 1;
            }
            s = start;
            while s <= n {
                result.push(s);
                s = s + 1;
            }
        }
        result
    }
}

}
