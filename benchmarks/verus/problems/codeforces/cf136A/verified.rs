use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn value_occurs(p: Seq<i32>, n: int, v: int) -> bool {
    exists|i: int| 0 <= i < n && p[i] == v
}

pub open spec fn is_permutation_1_to_n(p: Seq<i32>, n: int) -> bool {
    p.len() == n
        && 1 <= n <= 100
        && forall|i: int| 0 <= i < n ==> 1 <= #[trigger] p[i] <= n
        && forall|i: int, j: int| 0 <= i < j < n ==> p[i] != p[j]
        && forall|v: int| 1 <= v <= n ==> #[trigger] value_occurs(p, n, v)
}

impl Solution {
    pub fn inverse_presents(p: Vec<i32>, n: usize) -> (result: Vec<i32>)
        requires
            1 <= n <= 100,
            p.len() == n,
            is_permutation_1_to_n(p@, n as int),
        ensures
            result.len() == n,
            forall|i: int| 0 <= i < n as int ==> #[trigger] result@[p@[i] as int - 1] == (i + 1),
    {
        let mut result = Vec::new();
        let mut i = 0usize;
        while i < n
            invariant
                1 <= n <= 100,
                p.len() == n,
                is_permutation_1_to_n(p@, n as int),
                0 <= i <= n,
                result.len() == i,
                forall|j: int| 0 <= j < i ==> result@[j] == 0,
            decreases n - i,
        {
            result.push(0i32);
            i += 1;
        }
        i = 0usize;
        while i < n
            invariant
                1 <= n <= 100,
                p.len() == n,
                is_permutation_1_to_n(p@, n as int),
                result.len() == n,
                forall|k: int| 0 <= k < i ==> #[trigger] result@[p@[k] as int - 1] == (k + 1),
            decreases n - i,
        {
            let idx = (p[i] as usize) - 1;
            let ghost old_result = result@;
            result.set(idx, (i + 1) as i32);
            proof {
                assert(1 <= p@[i as int] <= n as int);
                assert(0 <= idx as int);
                assert((idx as int) < (n as int));
                assert(result@ == old_result.update(idx as int, (i + 1) as i32));
                assert forall|k: int| 0 <= k < i as int + 1 implies #[trigger] result@[p@[k] as int - 1] == (k + 1) by {
                    if k == i as int {
                        assert(p@[k] as int - 1 == idx as int);
                        assert(result@[idx as int] == (i + 1) as i32);
                    } else {
                        assert(0 <= k < i as int);
                        assert(old_result[p@[k] as int - 1] == (k + 1));
                        assert(p@[k] != p@[i as int]);
                        assert((p@[k] as int - 1) != (p@[i as int] as int - 1));
                        assert(result@[p@[k] as int - 1] == old_result[p@[k] as int - 1]);
                    }
                }
            }
            i += 1;
        }
        result
    }
}

}
