use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn elem_pair(s: Seq<i32>, i: int, j: int) -> (i32, i32) {
        (s[i], s[j])
    }

    pub open spec fn in_range(x: int, n: i32) -> bool {
        1 <= x <= n
    }

    pub open spec fn triple(s: Seq<i32>, i: int, j: int, k: int) -> (i32, i32, i32) {
        (s[i], s[j], s[k])
    }

    pub fn beautiful_array(n: i32) -> (result: Vec<i32>)
        requires
            1 <= n <= 1000,
        ensures
            result@.len() == n as int,
            forall |i: int| 0 <= i < result@.len() ==>
                1 <= #[trigger] result@[i] <= n,
            forall |i: int, j: int|
                0 <= i < j < result@.len() ==>
                #[trigger] Self::elem_pair(result@, i, j) == Self::elem_pair(result@, i, j)
                && result@[i] != result@[j],
            forall |x: int|
                #[trigger] Self::in_range(x, n) ==>
                exists |i: int| 0 <= i < result@.len() && result@[i] == x,
            forall |i: int, j: int, k: int|
                0 <= i < k < j < result@.len() ==>
                (#[trigger] Self::triple(result@, i, j, k) == Self::triple(result@, i, j, k))
                && 2 * result@[k] != result@[i] + result@[j],
    {
        let mut res = Vec::new();
        res.push(1);
        while res.len() < n as usize {
            let mut next = Vec::new();
            let mut i = 0usize;
            while i < res.len() {
                next.push(2 * res[i] - 1);
                i = i + 1;
            }
            let mut j = 0usize;
            while j < res.len() {
                next.push(2 * res[j]);
                j = j + 1;
            }
            res = next;
        }
        let mut out = Vec::new();
        let mut idx = 0usize;
        while idx < res.len() {
            if res[idx] <= n {
                out.push(res[idx]);
            }
            idx = idx + 1;
        }
        out
    }
}

}
