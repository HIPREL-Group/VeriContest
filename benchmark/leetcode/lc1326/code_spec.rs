use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn tap_left(ranges: Seq<i32>, t: int) -> int {
        t - ranges[t] as int
    }

    pub open spec fn tap_right(ranges: Seq<i32>, t: int) -> int {
        t + ranges[t] as int
    }

    pub open spec fn is_valid_covering(ranges: Seq<i32>, n: int, sel: Seq<int>) -> bool {
        sel.len() >= 1
        && (forall |k: int| 0 <= k < sel.len() ==> 0 <= #[trigger] sel[k] < ranges.len())
        && Self::tap_left(ranges, sel[0]) <= 0
        && Self::tap_right(ranges, sel[sel.len() - 1 as int]) >= n
        && (forall |k: int|
            #![trigger sel[k]]
            #![trigger sel[k + 1]]
            0 <= k < sel.len() - 1 ==>
            Self::tap_right(ranges, sel[k]) >= Self::tap_left(ranges, sel[k + 1]))
    }

    pub fn min_taps(n: i32, ranges: Vec<i32>) -> (res: i32)
        requires
            1 <= n <= 10_000,
            ranges.len() == n + 1,
            forall |i: int| 0 <= i < ranges.len() ==> 0 <= #[trigger] ranges[i] <= 100,
        ensures
            res == -1 || res >= 1,
            res == -1 ==> forall |sel: Seq<int>|
                !Self::is_valid_covering(ranges@, n as int, sel),
            res >= 1 ==> exists |sel: Seq<int>|
                #[trigger] Self::is_valid_covering(ranges@, n as int, sel)
                && sel.len() == res as nat,
            res >= 1 ==> forall |sel: Seq<int>|
                Self::is_valid_covering(ranges@, n as int, sel)
                ==> sel.len() >= res as nat,
    {
        let mut max_reach: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k <= n as usize {
            max_reach.push(0i32);
            k = k + 1;
        }

        let mut i: usize = 0;
        while i <= n as usize {
            let r = ranges[i];
            if r > 0 {
                let left: usize = if (i as i32) >= r { i - r as usize } else { 0 };
                let right: i32 = i as i32 + r;
                if right > max_reach[left] {
                    max_reach.set(left, right);
                }
            }
            i = i + 1;
        }

        let mut end: i32 = 0;
        let mut far: i32 = 0;
        let mut cnt: i32 = 0;

        let mut j: usize = 0;
        while j <= n as usize {
            if j as i32 > end {
                return -1;
            }
            if max_reach[j] > far {
                far = max_reach[j];
            }
            if j as i32 == end && end < n {
                if far <= end {
                    return -1;
                }
                end = far;
                cnt = cnt + 1;
            }
            j = j + 1;
        }

        cnt
    }
}

}
