use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_entry_at(k: int, n: int) -> int {
        if k < n {
            if k % 2 == 0 { 2 * k + 1 } else { 2 * k + 2 }
        } else {
            let j = k - n;
            if j % 2 == 0 { 2 * j + 2 } else { 2 * j + 1 }
        }
    }

    pub open spec fn spec_is_permutation(arr: Seq<i64>, n: int) -> bool {
        arr.len() == 2 * n
        && (forall|i: int| 0 <= i < 2 * n ==> 1 <= #[trigger] arr[i] <= 2 * n)
        && (forall|i: int, j: int| 0 <= i < j < 2 * n ==> #[trigger] arr[i] != #[trigger] arr[j])
    }

    pub open spec fn spec_circular_sum(a: Seq<i64>, n: int, start: int, count: int) -> int
        decreases count,
    {
        if count <= 0 {
            0int
        } else {
            a[start % (2 * n)] + Self::spec_circular_sum(a, n, start + 1, count - 1)
        }
    }

    pub open spec fn spec_all_sums_close(a: Seq<i64>, n: int) -> bool {
        forall|i: int, j: int|
            #![trigger Self::spec_circular_sum(a, n, i, n), Self::spec_circular_sum(a, n, j, n)]
            0 <= i < 2 * n && 0 <= j < 2 * n ==> {
                let diff = Self::spec_circular_sum(a, n, i, n) - Self::spec_circular_sum(a, n, j, n);
                -1 <= diff && diff <= 1
            }
    }

    pub fn almost_equal(n: usize) -> (res: Vec<i64>)
        requires
            1 <= n <= 100000,
        ensures
            n % 2 == 0 ==> res.len() == 0,
            n % 2 == 1 ==> (
                Self::spec_is_permutation(res@, n as int)
                && Self::spec_all_sums_close(res@, n as int)
            ),
    {
        if n % 2 == 0 {
            return Vec::new();
        }
        let mut res: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            if i % 2 == 0 {
                res.push((2 * i + 1) as i64);
            } else {
                res.push((2 * i + 2) as i64);
            }
            i = i + 1;
        }
        i = 0;
        while i < n {
            if i % 2 == 0 {
                res.push((2 * i + 2) as i64);
            } else {
                res.push((2 * i + 1) as i64);
            }
            i = i + 1;
        }
        res
    }
}

}
