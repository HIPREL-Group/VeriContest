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
        let mut remove_count: usize = 0;
        let mut add_count: usize = 0;
        let mut i: usize = 0;
        while i < s.len()
            invariant
                i <= s.len(),
                s.len() == f.len(),
                1 <= s.len() <= 100_000,
                forall|j: int| 0 <= j < s.len() ==> #[trigger] s[j] <= 1,
                forall|j: int| 0 <= j < f.len() ==> #[trigger] f[j] <= 1,
                remove_count as int == count_remove(s@, f@, i as int),
                add_count as int == count_add(s@, f@, i as int),
                remove_count <= i,
                add_count <= i,
            decreases s.len() - i,
        {
            proof {
                reveal_with_fuel(count_remove, 2);
                reveal_with_fuel(count_add, 2);
            }
            if s[i] == 1 && f[i] == 0 {
                remove_count = remove_count + 1;
            } else if s[i] == 0 && f[i] == 1 {
                add_count = add_count + 1;
            }
            i = i + 1;
        }
        if remove_count > add_count {
            remove_count
        } else {
            add_count
        }
    }
}

}
