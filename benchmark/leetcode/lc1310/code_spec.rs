use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn xor_fold(s: Seq<i32>) -> i32
        decreases s.len(),
    {
        if s.len() == 0 {
            0
        } else {
            Self::xor_fold(s.drop_last()) ^ s.last()
        }
    }

    pub open spec fn range_xor(arr: Seq<i32>, l: int, r: int) -> i32
        recommends
            0 <= l <= r < arr.len(),
    {
        Self::xor_fold(arr.subrange(l, r + 1))
    }

    pub fn xor_queries(arr: Vec<i32>, queries: Vec<Vec<i32>>) -> (answer: Vec<i32>)
        requires
            1 <= arr.len() <= 30_000,
            1 <= queries.len() <= 30_000,
            forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 1_000_000_000,
            forall |k: int|
                0 <= k < queries.len() ==> #[trigger] queries[k].len() == 2
                    && 0 <= queries[k][0] <= queries[k][1] < arr.len() as i32,
        ensures
            answer.len() == queries.len(),
            forall |k: int| 0 <= k < queries.len() ==> {
                let l = queries[k][0] as int;
                let r = queries[k][1] as int;
                #[trigger] answer[k] == Self::range_xor(arr@, l, r)
            },
    {
        let n = arr.len();
        let mut pref: Vec<i32> = Vec::new();
        pref.push(0);

        let mut i: usize = 0;
        while i < n {
            let next = pref[i] ^ arr[i];
            pref.push(next);
            i += 1;
        }

        let mut answer: Vec<i32> = Vec::new();
        let mut q: usize = 0;
        while q < queries.len() {
            let l_i32 = queries[q][0];
            let r_i32 = queries[q][1];
            let l = l_i32 as usize;
            let r = r_i32 as usize;
            let v = pref[r + 1] ^ pref[l];
            answer.push(v);
            q += 1;
        }

        answer
    }
}

}
