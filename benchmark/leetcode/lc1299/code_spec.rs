use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_max(s: Seq<i32>, start: int, end: int) -> int
        decreases end - start,
    {
        if start >= end {
            -1
        } else if end - start == 1 {
            s[start] as int
        } else {
            let rest_max = Self::spec_max(s, start + 1, end);
            if s[start] as int > rest_max { s[start] as int } else { rest_max }
        }
    }

    pub fn replace_elements(arr: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= arr.len() <= 10_000,
            forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 100_000,
        ensures
            result.len() == arr.len(),
            forall |i: int| 0 <= i < result.len() - 1 ==>
                result[i] as int == Self::spec_max(arr@, i + 1, arr.len() as int),
            arr.len() > 0 ==> result[result.len() - 1] == -1i32,
    {
        let mut result = arr;
        let n = result.len();
        let mut max_right: i32 = -1;
        let mut i: usize = n;

        while i > 0 {
            i = i - 1;
            let current = result[i];
            result.set(i, max_right);
            if current > max_right {
                max_right = current;
            }
        }

        result
    }
}

}
