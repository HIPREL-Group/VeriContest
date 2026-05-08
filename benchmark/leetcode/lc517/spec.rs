use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub closed spec fn sum_seq(s: Seq<i32>) -> int
        decreases s.len()
    {
        if s.len() == 0 {
            0
        } else {
            Self::sum_seq(s.drop_last()) + s.last() as int
        }
    }

    pub open spec fn prefix_sum(s: Seq<i32>, k: int) -> int
        recommends 0 <= k <= s.len()
        decreases k
    {
        if k <= 0 { 0 }
        else { Self::prefix_sum(s, k - 1) + s[k - 1] as int }
    }

    pub open spec fn running_deficit(s: Seq<i32>, avg: int, i: int) -> int
        recommends 0 <= i < s.len()
    {
        Self::prefix_sum(s, i + 1) - avg * (i + 1)
    }

    pub open spec fn abs(x: int) -> int {
        if x >= 0 { x } else { -x }
    }

    pub open spec fn trig(x: int) -> int { x }

    pub open spec fn feasible_k(machines: Seq<i32>, avg: int, k: int) -> bool {
        let n = machines.len() as int;
        k >= 0
        && (forall|i: int| 0 <= i < n ==> k >= machines[i] as int - avg)
        && (forall|i: int| 0 <= i < n ==> k >= Self::abs(Self::running_deficit(machines, avg, i)))
    }

    pub open spec fn spec_answer(machines: Seq<i32>, avg: int) -> int {
        choose|k: int|
            Self::feasible_k(machines, avg, k)
            && #[trigger] Self::trig(k) == k
            && (forall|k2: int|
                Self::feasible_k(machines, avg, k2)
                && #[trigger] Self::trig(k2) == k2
                ==> k <= k2)
    }

    pub fn find_min_moves(machines: Vec<i32>) -> (result: i32)
        requires
            1 <= machines.len() <= 10000,
            forall|i: int| 0 <= i < machines.len() ==> 0 <= #[trigger] machines[i] <= 100000,
        ensures
            result >= -1,
            Self::sum_seq(machines@) % (machines.len() as int) != 0 ==> result == -1,
            Self::sum_seq(machines@) % (machines.len() as int) == 0 ==>
                result as int == Self::spec_answer(
                    machines@,
                    Self::sum_seq(machines@) / (machines.len() as int),
                ),
    {
    }
}

}