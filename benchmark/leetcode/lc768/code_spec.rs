use vstd::prelude::*;
fn main() {}
verus! {
pub struct Solution;
impl Solution {
    pub open spec fn prefix_max_spec(s: Seq<i32>, i: int) -> int
        decreases i,
    {
        if i <= 0 { s[0] as int }
        else {
            let prev = Self::prefix_max_spec(s, i - 1);
            if s[i] as int > prev { s[i] as int } else { prev }
        }
    }

    pub open spec fn suffix_min_spec(s: Seq<i32>, i: int) -> int
        decreases s.len() - i,
    {
        if i >= s.len() - 1 { s[s.len() - 1] as int }
        else {
            let next = Self::suffix_min_spec(s, i + 1);
            if next > s[i] as int { s[i] as int } else { next }
        }
    }

    pub open spec fn is_chunk_boundary(s: Seq<i32>, i: int) -> bool {
        Self::prefix_max_spec(s, i) <= Self::suffix_min_spec(s, i + 1)
    }

    pub open spec fn count_boundaries(s: Seq<i32>, i: int) -> int
        decreases i + 1,
    {
        if i < 0 { 0 }
        else {
            Self::count_boundaries(s, i - 1)
                + if Self::is_chunk_boundary(s, i) { 1int } else { 0int }
        }
    }

    pub fn max_chunks_to_sorted(arr: Vec<i32>) -> (result: i32)
        requires
            1 <= arr.len() <= 2_000,
            forall|i: int| 0 <= i < arr.len() ==> 0 <= #[trigger] arr[i] <= 100_000_000,
        ensures
            result >= 1,
            result as int == 1 + Self::count_boundaries(arr@, arr@.len() as int - 2),
    {
        let n = arr.len();
        
        let mut suffix_min: Vec<i32> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            suffix_min.push(arr[i]);
            i += 1;
        }
        
        if n > 1 {
            let mut i: usize = n - 1;
            while i > 0 {
                i -= 1;
                if suffix_min[i + 1] < suffix_min[i] {
                    suffix_min.set(i, suffix_min[i + 1]);
                }
            }
        }
        
        let mut chunks: i32 = 1;
        let mut prefix_max = arr[0];
        let mut i: usize = 0;
        while i < n - 1 {
            if arr[i] > prefix_max {
                prefix_max = arr[i];
            }
            if prefix_max <= suffix_min[i + 1] {
                chunks += 1;
            }
            i += 1;
        }
        chunks
    }
}
}
