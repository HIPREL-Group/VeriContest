use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn sorted_non_decreasing(seq: Seq<i32>, n: int) -> bool {
    n <= seq.len()
        && forall|i: int| 0 <= i < n - 1 ==> #[trigger] seq[i] <= seq[i + 1]
}

pub open spec fn same_multiset(left: Seq<i32>, right: Seq<i32>) -> bool {
    left.len() == right.len() && left.to_multiset() =~= right.to_multiset()
}

impl Solution {
    pub fn gravity_flip(a: Vec<i32>, n: usize) -> (result: Vec<i32>)
        requires
            1 <= n <= 100,
            a.len() == n,
            forall|i: int| 0 <= i < n as int ==> 1 <= #[trigger] a[i] as int <= 100,
        ensures
            result.len() == n,
            sorted_non_decreasing(result@, n as int),
            same_multiset(result@, a@),
    {
        let mut arr = Vec::new();
        let mut i = 0usize;
        while i < n {
            arr.push(a[i]);
            i += 1;
        }
        i = 0usize;
        while i < n {
            let mut min_idx = i;
            let mut j = i + 1;
            while j < n {
                if arr[j] < arr[min_idx] {
                    min_idx = j;
                }
                j += 1;
            }
            if i != min_idx {
                let tmp = arr[i];
                arr.set(i, arr[min_idx]);
                arr.set(min_idx, tmp);
            }
            i += 1;
        }
        arr
    }
}

}
