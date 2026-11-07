use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn robin_gold_after_prefix(people: Seq<i64>, k: int, end: int) -> int
    recommends
        0 <= end <= people.len(),
        1 <= k,
    decreases end,
{
    if end <= 0 {
        0
    } else {
        let prev_gold = robin_gold_after_prefix(people, k, end - 1);
        let ai = people[end - 1] as int;
        if ai >= k {
            prev_gold + ai
        } else if ai == 0 && prev_gold > 0 {
            prev_gold - 1
        } else {
            prev_gold
        }
    }
}

pub open spec fn robin_helped_after_prefix(people: Seq<i64>, k: int, end: int) -> int
    recommends
        0 <= end <= people.len(),
        1 <= k,
    decreases end,
{
    if end <= 0 {
        0
    } else {
        let prev_helped = robin_helped_after_prefix(people, k, end - 1);
        let prev_gold = robin_gold_after_prefix(people, k, end - 1);
        let ai = people[end - 1] as int;
        if ai == 0 && prev_gold > 0 {
            prev_helped + 1
        } else {
            prev_helped
        }
    }
}

pub open spec fn robin_helped(people: Seq<i64>, k: int) -> int
    recommends
        1 <= k,
{
    robin_helped_after_prefix(people, k, people.len() as int)
}

impl Solution {
    pub fn count_people_helped(people: Vec<i64>, k: i64) -> (result: usize)
        requires
            1 <= people.len() <= 50,
            1 <= k <= 100,
            forall |i: int| 0 <= i < people.len() ==> 0 <= #[trigger] people[i] <= 100,
        ensures
            result as int == robin_helped(people@, k as int),
    {
        let mut gold: i64 = 0;
        let mut helped: usize = 0;
        let mut i: usize = 0;
        while i < people.len()
            invariant
                i <= people.len(),
                gold as int == robin_gold_after_prefix(people@, k as int, i as int),
                helped as int == robin_helped_after_prefix(people@, k as int, i as int),
                0 <= gold <= 100 * i as int,
                helped <= i,
                1 <= k <= 100,
                people.len() <= 50,
                forall |j: int| 0 <= j < people.len() ==> 0 <= #[trigger] people@[j] <= 100,
            decreases people.len() - i,
        {
            let ai = people[i];
            assert(0 <= ai <= 100);
            proof {
                reveal_with_fuel(robin_gold_after_prefix, 2);
                reveal_with_fuel(robin_helped_after_prefix, 2);
            }
            if ai >= k {
                assert(gold + ai <= 100 * i as int + 100);
                gold = gold + ai;
            } else if ai == 0 && gold > 0 {
                gold = gold - 1;
                helped = helped + 1;
            }
            i = i + 1;
        }
        proof {
            assert(i == people.len());
            assert(robin_helped(people@, k as int) == robin_helped_after_prefix(people@, k as int, people.len() as int));
        }
        helped
    }
}

}