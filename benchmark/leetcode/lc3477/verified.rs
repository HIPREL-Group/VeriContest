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

proof fn lemma_choose_characterization(used: Seq<i32>, baskets: Seq<i32>, fruit: i32, j: int)
    requires
        used.len() == baskets.len(),
        0 <= j <= baskets.len(),
    ensures
        choose_basket(used, baskets, fruit, j) == -1 ==> forall |t: int| j <= t < baskets.len() ==> !#[trigger] is_eligible(used, baskets, fruit, t),
        choose_basket(used, baskets, fruit, j) != -1 ==> (
            j <= choose_basket(used, baskets, fruit, j) < baskets.len()
            && is_eligible(used, baskets, fruit, choose_basket(used, baskets, fruit, j))
            && forall |t: int| j <= t < choose_basket(used, baskets, fruit, j) ==> !#[trigger] is_eligible(used, baskets, fruit, t)
        ),
    decreases baskets.len() - j,
{
    if j < baskets.len() {
        if is_eligible(used, baskets, fruit, j) {
        } else {
            lemma_choose_characterization(used, baskets, fruit, j + 1);
            let c = choose_basket(used, baskets, fruit, j + 1);
            assert(choose_basket(used, baskets, fruit, j) == c);
            if c == -1 {
                assert forall |t: int| j <= t < baskets.len() implies !is_eligible(used, baskets, fruit, t) by {
                    if t == j {
                        assert(!is_eligible(used, baskets, fruit, j));
                    } else {
                        assert(j + 1 <= t < baskets.len());
                    }
                }
            } else {
                assert(j < c < baskets.len());
                assert(is_eligible(used, baskets, fruit, c));
                assert forall |t: int| j <= t < c implies !is_eligible(used, baskets, fruit, t) by {
                    if t == j {
                        assert(!is_eligible(used, baskets, fruit, j));
                    } else {
                        assert(j + 1 <= t < c);
                    }
                }
            }
        }
    }
}

proof fn lemma_choose_unique(used: Seq<i32>, baskets: Seq<i32>, fruit: i32, j: int, idx: int)
    requires
        used.len() == baskets.len(),
        0 <= j <= idx < baskets.len(),
        is_eligible(used, baskets, fruit, idx),
        forall |t: int| j <= t < idx ==> !#[trigger] is_eligible(used, baskets, fruit, t),
    ensures
        choose_basket(used, baskets, fruit, j) == idx,
{
    lemma_choose_characterization(used, baskets, fruit, j);
    let c = choose_basket(used, baskets, fruit, j);
    if c == -1 {
        assert(!is_eligible(used, baskets, fruit, idx));
        assert(false);
    } else {
        if c < idx {
            assert(is_eligible(used, baskets, fruit, c));
            assert(!is_eligible(used, baskets, fruit, c));
            assert(false);
        }
        if idx < c {
            assert(!is_eligible(used, baskets, fruit, idx));
            assert(false);
        }
        assert(c == idx);
    }
}

proof fn lemma_prefix_step(fruits: Seq<i32>, baskets: Seq<i32>, k: int)
    requires
        fruits.len() == baskets.len(),
        0 <= k < fruits.len(),
    ensures
        spec_used_prefix(fruits, baskets, k + 1) == {
            let prev = spec_used_prefix(fruits, baskets, k);
            let c = choose_basket(prev, baskets, fruits[k], 0);
            if 0 <= c < prev.len() {
                prev.update(c, 1i32)
            } else {
                prev
            }
        },
        spec_unplaced_prefix(fruits, baskets, k + 1) == {
            let prev_used = spec_used_prefix(fruits, baskets, k);
            let c = choose_basket(prev_used, baskets, fruits[k], 0);
            spec_unplaced_prefix(fruits, baskets, k) + if c < 0 { 1int } else { 0int }
        },
{
    reveal_with_fuel(spec_used_prefix, 2);
    reveal_with_fuel(spec_unplaced_prefix, 2);
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
        while i < n
            invariant
                n == fruits.len(),
                n == baskets.len(),
                1 <= n <= 100,
                forall |k: int| 0 <= k < fruits.len() ==> 1 <= #[trigger] fruits[k] <= 1000,
                forall |k: int| 0 <= k < baskets.len() ==> 1 <= #[trigger] baskets[k] <= 1000,
                0 <= i <= n,
                used.len() == n,
                used@ == spec_used_prefix(fruits@, baskets@, i as int),
                unplaced as int == spec_unplaced_prefix(fruits@, baskets@, i as int),
                0 <= unplaced as int <= i as int,
            decreases n - i,
        {
            let fruit = fruits[i];
            let ghost prev_used = used@;
            let mut placed_idx: i32 = -1;
            let mut j: usize = 0;
            while j < n
                invariant
                    n == fruits.len(),
                    n == baskets.len(),
                    1 <= n <= 100,
                    0 <= i < n,
                    1 <= fruit <= 1000,
                    used.len() == n,
                    prev_used.len() == n,
                    forall |k: int| 0 <= k < baskets.len() ==> 1 <= #[trigger] baskets[k] <= 1000,
                    0 <= j <= n,
                    -1 <= placed_idx,
                    placed_idx < j as int,
                    placed_idx == -1 ==> (
                        used@ == prev_used
                        && forall |t: int| 0 <= t < j ==> !#[trigger] is_eligible(prev_used, baskets@, fruit, t)
                    ),
                    placed_idx != -1 ==> (
                        0 <= placed_idx < j as int
                        && is_eligible(prev_used, baskets@, fruit, placed_idx as int)
                        && used@ == prev_used.update(placed_idx as int, 1i32)
                        && forall |t: int| 0 <= t < placed_idx as int ==> !#[trigger] is_eligible(prev_used, baskets@, fruit, t)
                    ),
                decreases n - j,
            {
                if placed_idx == -1 && used[j] == 0 && baskets[j] >= fruit {
                    used.set(j, 1);
                    placed_idx = j as i32;
                    proof {
                        assert(used@ == prev_used.update(j as int, 1i32));
                        assert(is_eligible(prev_used, baskets@, fruit, j as int));
                    }
                }
                j += 1;
            }
            proof {
                let chosen = choose_basket(prev_used, baskets@, fruit, 0);
                lemma_choose_characterization(prev_used, baskets@, fruit, 0);
                if placed_idx == -1 {
                    assert(used@ == prev_used);
                    assert(forall |t: int| 0 <= t < n ==> !#[trigger] is_eligible(prev_used, baskets@, fruit, t));
                    if chosen != -1 {
                        assert(0 <= chosen < n);
                        assert(is_eligible(prev_used, baskets@, fruit, chosen));
                        assert(!is_eligible(prev_used, baskets@, fruit, chosen));
                        assert(false);
                    }
                    assert(chosen == -1);
                } else {
                    assert(0 <= placed_idx < n as int);
                    assert(is_eligible(prev_used, baskets@, fruit, placed_idx as int));
                    assert(forall |t: int| 0 <= t < placed_idx as int ==> !#[trigger] is_eligible(prev_used, baskets@, fruit, t));
                    lemma_choose_unique(prev_used, baskets@, fruit, 0, placed_idx as int);
                    assert(chosen == placed_idx as int);
                    assert(used@ == prev_used.update(chosen, 1i32));
                }
                lemma_prefix_step(fruits@, baskets@, i as int);
            }
            if placed_idx == -1 {
                unplaced += 1;
            }
            proof {
                let chosen = choose_basket(prev_used, baskets@, fruit, 0);
                if placed_idx == -1 {
                    assert(chosen == -1);
                    assert(used@ == prev_used);
                } else {
                    assert(chosen >= 0);
                    assert(used@ == prev_used.update(chosen, 1i32));
                }
                assert(used@ == spec_used_prefix(fruits@, baskets@, (i + 1) as int));
                if placed_idx == -1 {
                    assert(unplaced as int == spec_unplaced_prefix(fruits@, baskets@, i as int) + 1);
                } else {
                    assert(unplaced as int == spec_unplaced_prefix(fruits@, baskets@, i as int));
                }
                assert(unplaced as int == spec_unplaced_prefix(fruits@, baskets@, (i + 1) as int));
                assert(0 <= unplaced as int <= (i + 1) as int);
            }
            i += 1;
        }
        unplaced
    }
}

}
