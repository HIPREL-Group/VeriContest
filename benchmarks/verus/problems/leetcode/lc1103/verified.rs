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
        while idx < n
            invariant
                n == num_people as int,
                1 <= num_people <= 1000,
                result@.len() == idx as int,
                0 <= idx <= n,
                forall |k: int| 0 <= k < idx as int ==> (#[trigger] result@[k]) == 0i32,
            decreases n - idx,
        {
            result.push(0i32);
            idx = idx + 1;
        }

        proof {
            assert(Self::to_int_seq(result@) =~= Seq::new(num_people as nat, |_i: int| 0int));
        }

        let mut remaining = candies;
        let mut step: i32 = 0;

        while remaining > 0
            invariant
                1 <= candies <= 1_000_000_000,
                1 <= num_people <= 1000,
                n == num_people as int,
                result@.len() == num_people as int,
                0 <= remaining <= candies,
                0 <= step,
                step as int <= candies as int - remaining as int,
                forall |i: int| 0 <= i < num_people as int
                    ==> 0 <= (#[trigger] result@[i]) as int
                        <= candies as int - remaining as int,
                Self::distribute_helper(
                    remaining as int,
                    num_people as int,
                    step as int,
                    Self::to_int_seq(result@),
                ) == Self::distribute_spec(candies as int, num_people as int),
            decreases remaining as int,
        {
            let give: i32 = if remaining < step + 1 { remaining } else { step + 1 };
            let person_idx: i32 = step % num_people;
            let person: usize = person_idx as usize;

            let ghost old_acc = Self::to_int_seq(result@);

            proof {
                assert(result@[person as int] as int + give as int <= candies as int) by {
                    assert(result@[person as int] as int <= candies as int - remaining as int);
                    assert(give as int <= remaining as int);
                };
            }

            let old_val: i32 = result[person];
            result.set(person, old_val + give);
            remaining = remaining - give;
            step = step + 1;

            proof {
                assert(Self::to_int_seq(result@) =~= old_acc.update(
                    person_idx as int,
                    old_acc[person_idx as int] + give as int,
                ));
            }
        }

        proof {
            assert forall |i: int| 0 <= i < num_people as int
                implies (#[trigger] result@[i]) as int
                    == Self::distribute_spec(candies as int, num_people as int)[i]
            by {
                assert(Self::to_int_seq(result@)[i]
                    == Self::distribute_spec(candies as int, num_people as int)[i]);
            }
        }

        result
    }
}

}
