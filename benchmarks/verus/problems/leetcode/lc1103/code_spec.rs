use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn to_int_seq(s: Seq<i32>) -> Seq<int> {
        Seq::new(s.len(), |i: int| s[i] as int)
    }

    pub open spec fn distribute_helper(remaining: int, n: int, step: int, acc: Seq<int>) -> Seq<int>
        decreases remaining,
    {
        if remaining <= 0 || n <= 0 || step < 0 {
            acc
        } else {
            let give = if remaining < step + 1 { remaining } else { step + 1 };
            let person = step % n;
            Self::distribute_helper(
                remaining - give,
                n,
                step + 1,
                acc.update(person, acc[person] + give),
            )
        }
    }

    pub open spec fn distribute_spec(candies: int, n: int) -> Seq<int> {
        Self::distribute_helper(candies, n, 0, Seq::new(n as nat, |_i: int| 0int))
    }

    pub fn distribute_candies(candies: i32, num_people: i32) -> (result: Vec<i32>)
        requires
            1 <= candies <= 1_000_000_000,
            1 <= num_people <= 1000,
        ensures
            result@.len() == num_people as int,
            forall |i: int| 0 <= i < num_people as int
                ==> (#[trigger] result@[i]) as int
                    == Self::distribute_spec(candies as int, num_people as int)[i],
    {
        let n = num_people as usize;
        let mut result: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        while idx < n {
            result.push(0i32);
            idx = idx + 1;
        }
        let mut remaining = candies;
        let mut step: i32 = 0;
        while remaining > 0 {
            let give: i32 = if remaining < step + 1 { remaining } else { step + 1 };
            let person_idx: i32 = step % num_people;
            let person: usize = person_idx as usize;
            let old_val: i32 = result[person];
            result.set(person, old_val + give);
            remaining = remaining - give;
            step = step + 1;
        }
        result
    }
}

}
