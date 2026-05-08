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
        while i < n
            invariant
                n == mountain.len(),
                mountain.len() <= 2147483647usize,
                0 <= i <= n,
                forall |p: int| 0 <= p < result.len() ==> 1 <= #[trigger] result[p] < n as i32 - 1,
                forall |p: int| 0 <= p < result.len() ==> result[p] < i as i32,
                forall |p: int| 0 <= p < result.len() ==>
                    mountain[result[p] as int - 1] < mountain[result[p] as int] &&
                    mountain[result[p] as int] > mountain[result[p] as int + 1],
                forall |a: int, b: int| 0 <= a < b < result.len() ==> result[a] < result[b],
                forall |k: int|
                    1 <= k < i as int &&
                    k < n as int - 1 &&
                    mountain[k - 1] < #[trigger] mountain[k] &&
                    mountain[k] > mountain[k + 1]
                        ==> exists |p: int| 0 <= p < result.len() && result[p] as int == k,
            decreases n - i,
        {
            let ghost old_result = result@;
            assert(forall |k: int|
                1 <= k < i as int &&
                k < n as int - 1 &&
                mountain[k - 1] < #[trigger] mountain[k] &&
                mountain[k] > mountain[k + 1]
                    ==> exists |p: int| 0 <= p < old_result.len() && old_result[p] as int == k) by {
                assert forall |k: int|
                    1 <= k < i as int &&
                    k < n as int - 1 &&
                    mountain[k - 1] < #[trigger] mountain[k] &&
                    mountain[k] > mountain[k + 1]
                        implies exists |p: int| 0 <= p < old_result.len() && old_result[p] as int == k by {
                    assert(exists |p: int| 0 <= p < result.len() && result[p] as int == k);
                    let p = choose |p: int| 0 <= p < result.len() && result[p] as int == k;
                    assert(0 <= p < old_result.len());
                    assert(old_result[p] as int == k);
                };
            };

            let peak_here = i > 0 && i + 1 < n && mountain[i - 1] < mountain[i] && mountain[i] > mountain[i + 1];
            if i > 0 && i + 1 < n && mountain[i - 1] < mountain[i] && mountain[i] > mountain[i + 1] {
                result.push(i as i32);
                assert(result@ == old_result.push(i as i32));
            } else {
                assert(result@ == old_result);
            }

            assert(forall |k: int|
                1 <= k < i as int + 1 &&
                k < n as int - 1 &&
                mountain[k - 1] < #[trigger] mountain[k] &&
                mountain[k] > mountain[k + 1]
                    ==> exists |p: int| 0 <= p < result.len() && result[p] as int == k) by {
                assert forall |k: int|
                    1 <= k < i as int + 1 &&
                    k < n as int - 1 &&
                    mountain[k - 1] < #[trigger] mountain[k] &&
                    mountain[k] > mountain[k + 1]
                        implies exists |p: int| 0 <= p < result.len() && result[p] as int == k by {
                    if k < i as int {
                        assert(exists |p: int| 0 <= p < old_result.len() && old_result[p] as int == k);
                        let p = choose |p: int| 0 <= p < old_result.len() && old_result[p] as int == k;
                        assert(0 <= p < result.len());
                        assert(result[p] == old_result[p]);
                    } else {
                        assert(k == i as int);
                        assert(i > 0);
                        assert(i + 1 < n);
                        assert(peak_here);
                        let p = old_result.len() as int;
                        assert(0 <= p < result.len());
                        assert(result[p] as int == k);
                    }
                };
            }
            i = i + 1;
        }
        result
    }
}

}
