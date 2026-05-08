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
        while i < n {
            result.push(0i32);
            i += 1;
        }
        i = 0usize;
        while i < n {
            let idx = (p[i] as usize) - 1;
            result.set(idx, (i + 1) as i32);
            i += 1;
        }
        result
    }
}

}
