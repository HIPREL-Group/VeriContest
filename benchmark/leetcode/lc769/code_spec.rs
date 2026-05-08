use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn max_prefix(arr: Seq<i32>, i: int) -> int
        decreases i
    {
        if i < 0 {
            0
        } else if i == 0 {
            arr[0] as int
        } else {
            let prev = Self::max_prefix(arr, i - 1);
            if arr[i] as int > prev { arr[i] as int } else { prev }
        }
    }

    pub open spec fn count_chunks(arr: Seq<i32>, n: int) -> int
        decreases n
    {
        if n <= 0 {
            0
        } else {
            Self::count_chunks(arr, n - 1)
                + if Self::max_prefix(arr, n - 1) == n - 1 { 1int } else { 0int }
        }
    }

    pub fn max_chunks_to_sorted(arr: Vec<i32>) -> (res: i32)
        requires
            1 <= arr.len() <= 10,
            forall |i: int| 0 <= i < arr.len() ==> 0 <= #[trigger] arr[i] < arr.len(),
        ensures
            res as int == Self::count_chunks(arr@, arr.len() as int),
    {
        let mut max_so_far = 0i32;
        let mut chunks = 0i32;
        let mut i = 0usize;
        while i < arr.len() {
            if arr[i] > max_so_far {
                max_so_far = arr[i];
            }
            if max_so_far == i as i32 {
                chunks += 1;
            }
            i += 1;
        }
        chunks
    }
}

}
