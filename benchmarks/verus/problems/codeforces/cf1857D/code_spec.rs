use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn diff(a: Seq<i32>, b: Seq<i32>, i: int) -> int {
    a[i] as int - b[i] as int
}

pub open spec fn is_max_index(a: Seq<i32>, b: Seq<i32>, j: int) -> bool {
    0 <= j < a.len() && forall|m: int| 0 <= m < a.len() ==> diff(a, b, j) >= #[trigger] diff(a, b, m)
}

pub open spec fn sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] < s[j]
}

pub struct Solution;

impl Solution {
    pub fn strong_vertices(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
        requires
            2 <= a.len() <= 200_000,
            a.len() == b.len(),
            forall|j: int| 0 <= j < a.len() ==> -1_000_000_000 <= #[trigger] a[j] <= 1_000_000_000,
            forall|j: int| 0 <= j < b.len() ==> -1_000_000_000 <= #[trigger] b[j] <= 1_000_000_000,
        ensures
            result.len() >= 1,
            forall|k: int| 0 <= k < result.len() ==> 1 <= #[trigger] result[k] <= a.len() as i32
                && is_max_index(a@, b@, (result[k] - 1) as int),
            forall|j: int| 0 <= j < a.len() && is_max_index(a@, b@, j)
                ==> exists|k: int| 0 <= k < result.len() && #[trigger] result[k] == (j + 1) as i32,
            sorted(result@),
    {
        let n = a.len();
        let mut max_d: i32 = a[0] - b[0];
        let mut result: Vec<i32> = Vec::new();
        result.push(1);

        let mut i: usize = 1;
        while i < n {
            let d = a[i] - b[i];
            if d > max_d {
                max_d = d;
                result = Vec::new();
                result.push((i + 1) as i32);
            } else if d == max_d {
                result.push((i + 1) as i32);
            }
            i = i + 1;
        }

        result
    }
}

}
