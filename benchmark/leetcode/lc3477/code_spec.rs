use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_eligible(used: Seq<i32>, baskets: Seq<i32>, fruit: i32, idx: int) -> bool {
    0 <= idx < baskets.len() && idx < used.len() && used[idx] == 0 && baskets[idx] >= fruit
}

pub open spec fn choose_basket(used: Seq<i32>, baskets: Seq<i32>, fruit: i32, j: int) -> int
    recommends
        used.len() == baskets.len(),
        0 <= j <= baskets.len(),
    decreases baskets.len() - j,
{
    if j >= baskets.len() {
        -1
    } else if is_eligible(used, baskets, fruit, j) {
        j
    } else {
        choose_basket(used, baskets, fruit, j + 1)
    }
}

pub open spec fn spec_used_prefix(fruits: Seq<i32>, baskets: Seq<i32>, k: int) -> Seq<i32>
    recommends
        fruits.len() == baskets.len(),
        0 <= k <= fruits.len(),
    decreases k,
{
    if k <= 0 {
        Seq::new(baskets.len(), |i: int| 0i32)
    } else {
        let prev = spec_used_prefix(fruits, baskets, k - 1);
        let c = choose_basket(prev, baskets, fruits[k - 1], 0);
        if 0 <= c < prev.len() {
            prev.update(c, 1i32)
        } else {
            prev
        }
    }
}

pub open spec fn spec_unplaced_prefix(fruits: Seq<i32>, baskets: Seq<i32>, k: int) -> int
    recommends
        fruits.len() == baskets.len(),
        0 <= k <= fruits.len(),
    decreases k,
{
    if k <= 0 {
        0
    } else {
        let prev_used = spec_used_prefix(fruits, baskets, k - 1);
        let c = choose_basket(prev_used, baskets, fruits[k - 1], 0);
        spec_unplaced_prefix(fruits, baskets, k - 1) + if c < 0 { 1int } else { 0int }
    }
}

impl Solution {
    pub fn num_of_unplaced_fruits(fruits: Vec<i32>, baskets: Vec<i32>) -> (result: i32)
        requires
            1 <= fruits.len() <= 100,
            fruits.len() == baskets.len(),
            forall |i: int| 0 <= i < fruits.len() ==> 1 <= #[trigger] fruits[i] <= 1000,
            forall |i: int| 0 <= i < baskets.len() ==> 1 <= #[trigger] baskets[i] <= 1000,
        ensures
            result as int == spec_unplaced_prefix(fruits@, baskets@, fruits.len() as int),
    {
        let n = fruits.len();
        let mut used: Vec<i32> = vec![0; n];
        let mut unplaced: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            let fruit = fruits[i];
            let mut placed_idx: i32 = -1;
            let mut j: usize = 0;
            while j < n {
                if placed_idx == -1 && used[j] == 0 && baskets[j] >= fruit {
                    used.set(j, 1);
                    placed_idx = j as i32;
                }
                j += 1;
            }
            if placed_idx == -1 {
                unplaced += 1;
            }
            i += 1;
        }
        unplaced
    }
}

}
