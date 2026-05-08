use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn rev_prefix(s: Seq<i32>, k: int) -> Seq<i32> {
        Seq::new(k as nat, |i: int| s[k - 1 - i])
    }

    pub open spec fn apply_one_flip(s: Seq<i32>, k: i32) -> Seq<i32> {
        Self::rev_prefix(s, k as int).add(s.subrange(k as int, s.len() as int))
    }

    pub open spec fn apply_flips(s: Seq<i32>, flips: Seq<i32>) -> Seq<i32>
        decreases flips.len(),
    {
        if flips.len() == 0 {
            s
        } else if 1 <= flips[0] <= s.len() as i32 {
            Self::apply_flips(
                Self::apply_one_flip(s, flips[0]),
                flips.subrange(1, flips.len() as int),
            )
        } else {
            Self::apply_flips(s, flips.subrange(1, flips.len() as int))
        }
    }

    pub open spec fn value_in(s: Seq<i32>, v: i32) -> bool {
        exists |j: int| 0 <= j < s.len() && s[j] == v
    }

    pub fn pancake_sort(arr: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= arr.len() <= 100,
            forall |i: int| 0 <= i < arr.len() ==>
                1 <= #[trigger] arr[i] <= arr.len() as i32,
            forall |i: int, j: int|
                0 <= i < j < arr.len() ==> arr[i] != arr[j],
            forall |v: i32| 1 <= v <= arr.len() as i32 ==>
                #[trigger] Self::value_in(arr@, v),
        ensures
            forall |i: int| 0 <= i < result.len() ==>
                1 <= #[trigger] result[i] <= arr.len() as i32,
            result.len() <= 10 * arr.len(),
            forall |i: int, j: int|
                0 <= i < j < arr.len() ==>
                    Self::apply_flips(arr@, result@)[i]
                        <= Self::apply_flips(arr@, result@)[j],
    {
        let mut a = arr;
        let n = a.len();
        let mut result: Vec<i32> = Vec::new();
        let mut x = n as i32;
        while x >= 1
        {
            let mut i: usize = 0;
            while i < n && a[i] != x
            {
                i += 1;
            }
            let mut lo: usize = 0;
            let mut hi: usize = i;
            while lo < hi
            {
                let tmp = a[lo];
                a.set(lo, a[hi]);
                a.set(hi, tmp);
                lo += 1;
                hi -= 1;
            }
            result.push((i + 1) as i32);
            let rev_len = (x - 1) as usize;
            lo = 0;
            hi = rev_len;
            while lo < hi
            {
                let tmp = a[lo];
                a.set(lo, a[hi]);
                a.set(hi, tmp);
                lo += 1;
                hi -= 1;
            }
            result.push(x);
            x -= 1;
        }
        result
    }
}

}
