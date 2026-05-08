use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn kids_with_candies(candies: Vec<i32>, extra_candies: i32) -> (result: Vec<bool>)
        requires
            2 <= candies.len() <= 100,
            forall |i: int| 0 <= i < candies.len() ==> 1 <= #[trigger] candies[i] <= 100,
            1 <= extra_candies <= 50,
        ensures
            result.len() == candies.len(),
            forall |i: int| 0 <= i < candies.len() ==>
                #[trigger] result[i] ==
                    (forall |j: int| 0 <= j < candies.len() ==> candies[i] + extra_candies >= candies[j]),
    {
        let n = candies.len();
        let mut max_candies = candies[0];
        let mut max_index: usize = 0;
        let mut i: usize = 1;

        while i < n
            invariant
                n == candies.len(),
                2 <= n <= 100,
                1 <= i <= n,
                0 <= max_index < i,
                max_candies == candies[max_index as int],
                forall |j: int| 0 <= j < n ==> 1 <= #[trigger] candies[j] <= 100,
                forall |j: int| 0 <= j < i ==> candies[j] <= max_candies,
            decreases n - i,
        {
            if candies[i] > max_candies {
                proof {
                    assert forall |j: int| 0 <= j < i + 1 implies candies[j] <= candies[i as int] by {
                        if j < i as int {
                            assert(candies[j] <= max_candies);
                            assert(max_candies < candies[i as int]);
                        } else {
                            assert(j == i as int);
                        }
                    }
                }
                max_candies = candies[i];
                max_index = i;
            } else {
                proof {
                    assert forall |j: int| 0 <= j < i + 1 implies candies[j] <= max_candies by {
                        if j < i as int {
                            assert(candies[j] <= max_candies);
                        } else {
                            assert(j == i as int);
                            assert(candies[i as int] <= max_candies);
                        }
                    }
                }
            }
            i = i + 1;
        }

        let threshold = candies[max_index] - extra_candies;
        let mut result: Vec<bool> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                n == candies.len(),
                2 <= n <= 100,
                0 <= k <= n,
                result.len() == k,
                0 <= max_index < n,
                max_candies == candies[max_index as int],
                threshold == max_candies - extra_candies,
                forall |j: int| 0 <= j < n ==> 1 <= #[trigger] candies[j] <= 100,
                forall |j: int| 0 <= j < n ==> candies[j] <= max_candies,
                forall |i: int| 0 <= i < k ==>
                    #[trigger] result[i] ==
                        (forall |j: int| 0 <= j < n ==> candies[i] + extra_candies >= candies[j]),
            decreases n - k,
        {
            let can_have_most = candies[k] >= threshold;

            proof {
                if can_have_most {
                    assert(candies[k as int] + extra_candies >= max_candies);
                    assert forall |j: int| 0 <= j < n implies candies[k as int] + extra_candies >= candies[j] by {
                        assert(candies[j] <= max_candies);
                    }
                    assert(can_have_most == (forall |j: int| 0 <= j < n ==> candies[k as int] + extra_candies >= candies[j]));
                } else {
                    assert(candies[k as int] + extra_candies < max_candies);
                    assert(!(forall |j: int| 0 <= j < n ==> candies[k as int] + extra_candies >= candies[j])) by {
                        assert(!(candies[k as int] + extra_candies >= candies[max_index as int]));
                    }
                    assert(can_have_most == (forall |j: int| 0 <= j < n ==> candies[k as int] + extra_candies >= candies[j]));
                }
            }

            let ghost result_before = result@;
            result.push(can_have_most);
            proof {
                assert(result@ == result_before.push(can_have_most));
                assert forall |i: int| 0 <= i < result.len() implies
                    #[trigger] result[i] ==
                        (forall |j: int| 0 <= j < n ==> candies[i] + extra_candies >= candies[j]) by {
                    if i < k as int {
                        assert(result[i] == result_before[i]);
                    } else {
                        assert(i == k as int);
                    }
                }
            }

            k = k + 1;
        }

        result
    }
}

}