use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn student_can_attend(days: Seq<Vec<bool>>, i: int, d: int) -> bool {
    days[i]@[d]
}

pub open spec fn count_can_attend_one(days: Seq<Vec<bool>>, d: int, end: int) -> int
    decreases end
{
    if end <= 0 { 0 }
    else { count_can_attend_one(days, d, end - 1) + (if student_can_attend(days, end - 1, d) { 1int } else { 0int }) }
}

pub open spec fn count_can_attend_either(days: Seq<Vec<bool>>, d1: int, d2: int, end: int) -> int
    decreases end
{
    if end <= 0 { 0 }
    else { count_can_attend_either(days, d1, d2, end - 1) + (if student_can_attend(days, end - 1, d1) || student_can_attend(days, end - 1, d2) { 1int } else { 0int }) }
}

pub open spec fn is_valid_pair(n: usize, days: Seq<Vec<bool>>, d1: int, d2: int) -> bool {
    0 <= d1 && d1 < d2 && d2 < 5 &&
    count_can_attend_either(days, d1, d2, n as int) == n as int &&
    count_can_attend_one(days, d1, n as int) >= (n / 2) as int &&
    count_can_attend_one(days, d2, n as int) >= (n / 2) as int
}

pub open spec fn has_valid_pair(n: usize, days: Seq<Vec<bool>>) -> bool {
    exists|d1: int, d2: int| is_valid_pair(n, days, d1, d2)
}

pub struct Solution;

impl Solution {
    pub fn groups(n: usize, days: Vec<Vec<bool>>) -> (res: bool)
        requires
            2 <= n && n <= 1000,
            n % 2 == 0,
            days.len() == n,
            forall|i: int| 0 <= i && i < n ==> days@[i].len() == 5,
            forall|i: int| 0 <= i && i < n ==>
                days@[i]@[0] || days@[i]@[1] || days@[i]@[2] || days@[i]@[3] || days@[i]@[4],
        ensures
            res == has_valid_pair(n, days@)
    {
        let mut found = false;
        let mut d1: usize = 0;
        while d1 < 5 && !found
            invariant
                0 <= (d1 as int) && (d1 as int) <= 5,
                days.len() == n,
                n % 2 == 0,
                forall|i: int| 0 <= i && i < n ==> days@[i].len() == 5,
                forall|i: int| 0 <= i && i < n ==>
                    days@[i]@[0] || days@[i]@[1] || days@[i]@[2] || days@[i]@[3] || days@[i]@[4],
                found ==> has_valid_pair(n, days@),
                !found ==> forall|d_a: int, d_b: int| 0 <= d_a && d_a < (d1 as int) && d_a < d_b && d_b < 5 ==> !is_valid_pair(n, days@, d_a, d_b)
            decreases 5 - (d1 as int)
        {
            let mut d2: usize = d1 + 1;
            while d2 < 5 && !found
                invariant
                    0 <= (d1 as int) && (d1 as int) < 5,
                    (d1 as int) + 1 <= (d2 as int) && (d2 as int) <= 5,
                    days.len() == n,
                    n % 2 == 0,
                    forall|i: int| 0 <= i && i < n ==> days@[i].len() == 5,
                    forall|i: int| 0 <= i && i < n ==>
                        days@[i]@[0] || days@[i]@[1] || days@[i]@[2] || days@[i]@[3] || days@[i]@[4],
                    found ==> has_valid_pair(n, days@),
                    !found ==> forall|d_a: int, d_b: int| 0 <= d_a && d_a < (d1 as int) && d_a < d_b && d_b < 5 ==> !is_valid_pair(n, days@, d_a, d_b),
                    !found ==> forall|d_b: int| (d1 as int) < d_b && d_b < (d2 as int) ==> !is_valid_pair(n, days@, d1 as int, d_b)
                decreases 5 - (d2 as int)
            {
                let mut either: usize = 0;
                let mut can_d1: usize = 0;
                let mut can_d2: usize = 0;
                let mut i: usize = 0;
                while i < n
                    invariant
                        0 <= (d1 as int) && (d1 as int) < (d2 as int) && (d2 as int) < 5,
                        0 <= i && i <= n,
                        either <= i,
                        can_d1 <= i,
                        can_d2 <= i,
                        days.len() == n,
                        n % 2 == 0,
                        forall|k: int| 0 <= k && k < n ==> days@[k].len() == 5,
                        forall|k: int| 0 <= k && k < n ==>
                            days@[k]@[0] || days@[k]@[1] || days@[k]@[2] || days@[k]@[3] || days@[k]@[4],
                        (either as int) == count_can_attend_either(days@, d1 as int, d2 as int, i as int),
                        (can_d1 as int) == count_can_attend_one(days@, d1 as int, i as int),
                        (can_d2 as int) == count_can_attend_one(days@, d2 as int, i as int)
                    decreases n - i
                {
                    let c1 = days[i][d1];
                    let c2 = days[i][d2];
                    if c1 || c2 {
                        either += 1;
                    }
                    if c1 {
                        can_d1 += 1;
                    }
                    if c2 {
                        can_d2 += 1;
                    }
                    i += 1;
                }
                
                if either == n && can_d1 >= n / 2 && can_d2 >= n / 2 {
                    found = true;
                    proof {
                        assert(is_valid_pair(n, days@, d1 as int, d2 as int));
                        assert(has_valid_pair(n, days@));
                    }
                }
                d2 += 1;
            }
            d1 += 1;
        }
        found
    }
}
}
