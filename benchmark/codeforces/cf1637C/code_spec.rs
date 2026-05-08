use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn ceil_half_i64(x: i64) -> int {
        ((x + 1) / 2) as int
    }

    pub open spec fn prefix_sum_ceil_half(a: Seq<i64>, end: int) -> int
        recommends
            1 <= end <= a.len(),
        decreases
            end,
    {
        if end <= 1 {
            0
        } else {
            Self::prefix_sum_ceil_half(a, end - 1) + Self::ceil_half_i64(a[end - 1])
        }
    }

    pub open spec fn sum_middle_ops(a: Seq<i64>) -> int
        recommends
            a.len() >= 3,
    {
        Self::prefix_sum_ceil_half(a, a.len() - 1)
    }

    pub open spec fn stones_impossible(a: Seq<i64>) -> bool {
        let n = a.len();
        if n == 3 {
            (a[1] as int) % 2 == 1
        } else {
            forall|i: int|
                #![trigger a[i]]
                1 <= i <= n - 2 ==> a[i] == 1
        }
    }

    pub open spec fn minimum_stone_ops_answer(a: Seq<i64>) -> int
        recommends
            a.len() >= 3,
            !Self::stones_impossible(a),
    {
        let n = a.len();
        if n == 3 {
            a[1] as int / 2
        } else {
            Self::sum_middle_ops(a)
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn minimum_stone_operations(a: Vec<i64>) -> (r: Option<i64>)
        requires
            3 <= a.len() <= 100_000,
            forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] && a[i] <= 1_000_000_000,
        ensures
            r == None::<i64> <==> Self::stones_impossible(a@),
            r != None::<i64> ==> (r->Some_0 as int) == Self::minimum_stone_ops_answer(a@),
    {
        let n = a.len();
        if n == 3 {
            let m = a[1];
            if m % 2 == 1 {
                return None;
            }
            return Some(m / 2);
        }
        let mut all_one = true;
        let mut i: usize = 1;
        while i < n - 1 {
            if a[i] != 1 {
                all_one = false;
            }
            i = i + 1;
        }
        if all_one {
            return None;
        }
        let mut s: i64 = 0;
        let mut j: usize = 1;
        while j < n - 1 {
            s = s + (a[j] + 1) / 2;
            j = j + 1;
        }
        Some(s)
    }
}

}
