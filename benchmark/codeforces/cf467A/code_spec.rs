use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn room_fits_two(p: i64, q: i64) -> bool {
    (q as int) - (p as int) >= 2
}

pub open spec fn accommodation_count_prefix(p: Seq<i64>, q: Seq<i64>, k: int) -> int
    recommends
        p.len() == q.len(),
        0 <= k <= p.len(),
    decreases k,
{
    if k <= 0 {
        0int
    } else {
        accommodation_count_prefix(p, q, k - 1) + if room_fits_two(p[k - 1], q[k - 1]) { 1int } else { 0int }
    }
}

impl Solution {
    pub fn count_accommodation_rooms(p: Vec<i64>, q: Vec<i64>) -> (result: usize)
        requires
            1 <= p.len() <= 100,
            p.len() == q.len(),
            forall|j: int| 0 <= j < p.len() ==> 0 <= (#[trigger] p[j] as int) && (p[j] as int) <= (q[j] as int) && (q[j] as int) <= 100,
        ensures
            result as int == accommodation_count_prefix(p@, q@, p.len() as int),
    {
        let n = p.len();
        let mut cnt = 0usize;
        let mut i = 0usize;
        while i < n {
            let fits = q[i] - p[i] >= 2;
            if fits {
                cnt = cnt + 1;
            }
            i = i + 1;
        }
        cnt
    }
}

}
