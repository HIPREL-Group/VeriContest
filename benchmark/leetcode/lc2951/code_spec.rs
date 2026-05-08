use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn find_peaks(mountain: Vec<i32>) -> (result: Vec<i32>)
        requires
            mountain.len() <= 2147483647usize,
        ensures
            forall |p: int| 0 <= p < result.len() ==> 1 <= #[trigger] result[p] < mountain.len() as i32 - 1,
            forall |p: int| 0 <= p < result.len() ==>
                mountain[result[p] as int - 1] < mountain[result[p] as int] &&
                mountain[result[p] as int] > mountain[result[p] as int + 1],
            forall |a: int, b: int| 0 <= a < b < result.len() ==> result[a] < result[b],
            forall |i: int|
                1 <= i < mountain.len() as int - 1 &&
                mountain[i - 1] < #[trigger] mountain[i] &&
                mountain[i] > mountain[i + 1]
                    ==> exists |p: int| 0 <= p < result.len() && result[p] as int == i,
    {
        let n = mountain.len();
        let mut result: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            if i > 0 && i + 1 < n && mountain[i - 1] < mountain[i] && mountain[i] > mountain[i + 1] {
                result.push(i as i32);
            }
            i = i + 1;
        }
        result
    }
}

}
