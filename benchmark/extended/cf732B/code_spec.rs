use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn walk_feasible(a: Seq<i32>, b: Seq<i32>, k: int) -> bool {
    &&& a.len() == b.len()
    &&& forall|i: int| 0 <= i < a.len() ==> #[trigger] b[i] >= a[i]
    &&& forall|i: int| 0 <= i < a.len() - 1 ==> #[trigger] b[i] + b[i + 1] >= k
}

pub open spec fn greedy_walk_at(a: Seq<i32>, k: int, inat: nat) -> int
    recommends
        (inat as int) < a.len(),
    decreases
        inat,
{
    let i = inat as int;
    if inat == 0nat {
        if (a[0] as int) >= k - k {
            a[0] as int
        } else {
            k - k
        }
    } else {
        let prev = greedy_walk_at(a, k, (inat - 1) as nat);
        if (a[i] as int) >= k - prev {
            a[i] as int
        } else {
            k - prev
        }
    }
}

pub open spec fn greedy_additional_prefix(a: Seq<i32>, k: int, end: nat) -> int
    recommends
        (end as int) <= a.len(),
    decreases
        end,
{
    if end == 0nat {
        0
    } else {
        let last = (end - 1) as int;
        greedy_additional_prefix(a, k, (end - 1) as nat) + (greedy_walk_at(a, k, (end - 1) as nat) - a[last] as int)
    }
}

pub open spec fn spec_total_extra(a: Seq<i32>, b: Seq<i32>, end: nat) -> int
    recommends
        (end as int) <= a.len(),
        (end as int) <= b.len(),
    decreases
        end,
{
    if end == 0nat {
        0
    } else {
        let last = (end - 1) as int;
        spec_total_extra(a, b, (end - 1) as nat) + (b[last] as int - a[last] as int)
    }
}

impl Solution {
    pub fn cormen_walk_schedule(a: Vec<i32>, k: i32) -> (result: (i64, Vec<i32>))
        requires
            1 <= a.len() && a.len() <= 500,
            1 <= k <= 500,
            forall|i: int| 0 <= i < a.len() ==> 0 <= #[trigger] a[i] && a[i] <= 500,
        ensures
            walk_feasible(a@, result.1@, k as int),
            result.0 as int == spec_total_extra(a@, result.1@, a.len() as nat),
            forall|bp: Seq<i32>| walk_feasible(a@, bp, k as int) ==>
                result.0 as int <= spec_total_extra(a@, bp, a.len() as nat),
    {
        let n = a.len();
        let mut b: Vec<i32> = Vec::new();
        let mut total: i64 = 0;
        let mut prev: i32 = k;
        let mut i: usize = 0;
        while i < n {
            let ai = a[i];
            let kd = k as i64;
            let pred = prev as i64;
            let bi = if (ai as i64) >= kd - pred { ai } else { (kd - pred) as i32 };
            total = total + (bi as i64 - ai as i64);
            b.push(bi);
            prev = bi;
            i = i + 1;
        }
        (total, b)
    }
}

}
