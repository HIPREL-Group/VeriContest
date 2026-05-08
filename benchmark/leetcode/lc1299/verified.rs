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

    proof fn spec_max_bounded(s: Seq<i32>, start: int, end: int)
        requires
            0 <= start,
            end <= s.len(),
            forall |k: int| 0 <= k < s.len() ==> 1 <= #[trigger] s[k] <= 100_000,
        ensures
            -1 <= Self::spec_max(s, start, end) <= 100_000,
        decreases end - start,
    {
        if start >= end {
        } else if end - start == 1 {
        } else {
            Self::spec_max_bounded(s, start + 1, end);
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
        let ghost orig = arr@;
        let mut result = arr;
        let n = result.len();
        let mut max_right: i32 = -1;
        let mut i: usize = n;

        while i > 0
            invariant
                0 <= i <= n,
                n == result.len(),
                result.len() == orig.len(),
                orig.len() <= 10_000,
                orig.len() >= 1,
                forall |k: int| 0 <= k < orig.len() ==> 1 <= #[trigger] orig[k] <= 100_000,
                max_right as int == Self::spec_max(orig, i as int, n as int),
                forall |k: int| i as int <= k < n as int - 1 ==>
                    result[k] as int == Self::spec_max(orig, k + 1, n as int),
                i < n ==> result[n as int - 1] == -1i32,
                forall |k: int| 0 <= k < i as int ==> result[k] == #[trigger] orig[k],
                -1 <= max_right <= 100_000,
            decreases i,
        {
            i = i - 1;
            let current = result[i];

            proof {
                assert(current == orig[i as int]);
            }

            result.set(i, max_right);

            let ghost old_max = max_right as int;

            if current > max_right {
                max_right = current;
            }

            proof {
                Self::spec_max_bounded(orig, i as int, n as int);
            }
        }

        result
    }
}

}
