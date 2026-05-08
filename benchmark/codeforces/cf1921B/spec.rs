use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_remove(s: Seq<u8>, f: Seq<u8>, end: int) -> int
    recommends
        0 <= end <= s.len(),
        s.len() == f.len(),
    decreases end,
{
    if end <= 0 {
        0int
    } else {
        let prev = count_remove(s, f, end - 1);
        if s[end - 1] == 1u8 && f[end - 1] == 0u8 {
            prev + 1
        } else {
            prev
        }
    }
}

pub open spec fn count_add(s: Seq<u8>, f: Seq<u8>, end: int) -> int
    recommends
        0 <= end <= s.len(),
        s.len() == f.len(),
    decreases end,
{
    if end <= 0 {
        0int
    } else {
        let prev = count_add(s, f, end - 1);
        if s[end - 1] == 0u8 && f[end - 1] == 1u8 {
            prev + 1
        } else {
            prev
        }
    }
}

impl Solution {
    pub fn min_days(s: Vec<u8>, f: Vec<u8>) -> (result: usize)
        requires
            1 <= s.len() <= 100_000,
            s.len() == f.len(),
            forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] <= 1,
            forall|i: int| 0 <= i < f.len() ==> #[trigger] f[i] <= 1,
        ensures
            ({
                let r = count_remove(s@, f@, s.len() as int);
                let a = count_add(s@, f@, s.len() as int);
                result as int == if r > a { r } else { a }
            }),
    {
    }
}

}
