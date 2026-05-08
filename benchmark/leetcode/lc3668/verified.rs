use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn filtered_prefix(order: Seq<i32>, friends: Seq<i32>, k: nat) -> Seq<i32>
        decreases k,
    {
        if k == 0 {
            seq![]
        } else {
            let prev = Solution::filtered_prefix(order, friends, (k - 1) as nat);
            if friends.contains(order[(k - 1) as int]) {
                prev.push(order[(k - 1) as int])
            } else {
                prev
            }
        }
    }

    pub open spec fn finishing_order(order: Seq<i32>, friends: Seq<i32>) -> Seq<i32>
    {
        Solution::filtered_prefix(order, friends, order.len())
    }

    pub fn recover_order(order: Vec<i32>, friends: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= order.len() <= 100,
            forall |i: int| 0 <= i < order.len() ==> 1 <= #[trigger] order[i] <= order.len() as i32,
            forall |i: int, j: int| 0 <= i < j < order.len() ==> order[i] != order[j],
            forall |id: int| 1 <= id <= order.len() ==> #[trigger] order@.contains(id as i32),
            1 <= friends.len() <= 8,
            friends.len() <= order.len(),
            forall |i: int| 0 <= i < friends.len() ==> 1 <= #[trigger] friends[i] <= order.len() as i32,
            forall |i: int, j: int| 0 <= i < j < friends.len() ==> friends[i] < friends[j],
            forall |i: int| 0 <= i < friends.len() ==> order@.contains(#[trigger] friends[i]),
        ensures
            result@ == Solution::finishing_order(order@, friends@),
    {
        let mut result: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < order.len()
            invariant
                i <= order.len(),
                result@ == Solution::filtered_prefix(order@, friends@, i as nat),
            decreases order.len() - i,
        {
            let candidate = order[i];
            let mut j: usize = 0;
            let mut found = false;
            while j < friends.len()
                invariant
                    j <= friends.len(),
                    candidate == order@[i as int],
                    found ==> exists |q: int| 0 <= q < j && friends@[q] == candidate,
                    !found ==> forall |q: int| 0 <= q < j ==> friends@[q] != candidate,
                decreases friends.len() - j,
            {
                if friends[j] == candidate {
                    found = true;
                }
                j = j + 1;
            }

            assert(j == friends.len());

            assert(found ==> friends@.contains(candidate)) by {
                if found {
                    let q = choose |q: int| 0 <= q < j && friends@[q] == candidate;
                    assert(0 <= q < friends.len());
                }
            }

            assert(!found ==> !friends@.contains(candidate)) by {
                if !found {
                    if friends@.contains(candidate) {
                        let q = choose |q: int| 0 <= q < friends.len() && friends@[q] == candidate;
                        assert(0 <= q < j);
                        assert(forall |t: int| 0 <= t < j ==> friends@[t] != candidate);
                        assert(friends@[q] != candidate);
                        assert(false);
                    }
                }
            }

            assert(found <==> friends@.contains(candidate));

            let ghost prev = result@;

            if found {
                result.push(candidate);
                assert(result@ == prev.push(candidate));
            } else {
                assert(result@ == prev);
            }

            assert(prev == Solution::filtered_prefix(order@, friends@, i as nat));
            assert(candidate == order@[i as int]);

            assert(Solution::filtered_prefix(order@, friends@, i as nat + 1)
                == if friends@.contains(order@[i as int]) {
                    Solution::filtered_prefix(order@, friends@, i as nat).push(order@[i as int])
                } else {
                    Solution::filtered_prefix(order@, friends@, i as nat)
                });

            if found {
                assert(friends@.contains(order@[i as int]));
                assert(result@ == Solution::filtered_prefix(order@, friends@, i as nat + 1));
            } else {
                assert(!friends@.contains(order@[i as int]));
                assert(result@ == Solution::filtered_prefix(order@, friends@, i as nat + 1));
            }

            i = i + 1;
        }

        assert(i == order.len());
        assert(result@ == Solution::filtered_prefix(order@, friends@, order.len() as nat));
        result
    }
}

}
