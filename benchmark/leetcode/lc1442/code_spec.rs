use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn xor_range(arr: Seq<i32>, start: int, end: int) -> i32
    decreases end - start
{
    if start >= end {
        0i32
    } else {
        xor_range(arr, start, end - 1) ^ arr[end - 1]
    }
}

pub open spec fn count_k(arr: Seq<i32>, i: int, k: int) -> int
    decreases arr.len() - k
{
    if k >= arr.len() {
        0
    } else {
        (if xor_range(arr, i, k + 1) == 0i32 { k - i } else { 0int })
        + count_k(arr, i, k + 1)
    }
}

pub open spec fn count_all(arr: Seq<i32>, i: int) -> int
    decreases arr.len() - i
{
    if i >= arr.len() {
        0
    } else {
        count_k(arr, i, i + 1) + count_all(arr, i + 1)
    }
}

impl Solution {
    pub fn count_triplets(arr: Vec<i32>) -> (res: i32)
        requires
            1 <= arr.len() <= 300,
            forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 100_000_000,
        ensures
            res as int == count_all(arr@, 0),
    {
        let n = arr.len();
        let mut prefix: Vec<i32> = Vec::new();
        prefix.push(0);
        let mut i: usize = 0;
        while i < n {
            let prev = prefix[i];
            prefix.push(prev ^ arr[i]);
            i = i + 1;
        }
        let mut keys: Vec<i32> = Vec::new();
        let mut cnts: Vec<i32> = Vec::new();
        let mut sums: Vec<i32> = Vec::new();
        let mut count: i32 = 0;
        let mut m: usize = 0;
        while m <= n {
            let pv = prefix[m];
            let mut found: bool = false;
            let mut idx: usize = 0;
            let keys_len = keys.len();
            while idx < keys_len {
                if keys[idx] == pv {
                    found = true;
                    if m > 0 {
                        count = count + cnts[idx] * ((m as i32) - 1) - sums[idx];
                    }
                    cnts.set(idx, cnts[idx] + 1);
                    sums.set(idx, sums[idx] + m as i32);
                    idx = keys_len;
                } else {
                    idx = idx + 1;
                }
            }
            if !found {
                keys.push(pv);
                cnts.push(1);
                sums.push(m as i32);
            }
            m = m + 1;
        }
        count
    }
}

}
