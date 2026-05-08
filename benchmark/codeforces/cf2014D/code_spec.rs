use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_overlaps_window(start: int, d: int, l: int, r: int) -> bool {
        start <= r && l <= start + d - 1
    }

    pub open spec fn spec_overlap_count_prefix(start: int, d: int, left: Seq<i32>, right: Seq<i32>, upto: int) -> int
        recommends
            0 <= upto <= left.len(),
            left.len() == right.len(),
        decreases upto,
    {
        if upto <= 0 {
            0
        } else {
            Self::spec_overlap_count_prefix(start, d, left, right, upto - 1)
                + if Self::spec_overlaps_window(start, d, left[upto - 1] as int, right[upto - 1] as int) {
                    1int
                } else {
                    0int
                }
        }
    }

    pub open spec fn spec_overlap_count(start: int, d: int, left: Seq<i32>, right: Seq<i32>) -> int
        recommends
            left.len() == right.len(),
    {
        Self::spec_overlap_count_prefix(start, d, left, right, left.len() as int)
    }

    pub fn overlaps_window(start: i32, d: i32, l: i32, r: i32) -> (res: bool)
        requires
            1 <= d,
        ensures
            res == Self::spec_overlaps_window(start as int, d as int, l as int, r as int),
    {
        (start as i64) <= (r as i64) && (l as i64) <= (start as i64) + (d as i64) - 1
    }

    pub fn overlap_count(start: i32, d: i32, left: &Vec<i32>, right: &Vec<i32>) -> (res: i32)
        requires
            1 <= d,
            left.len() == right.len(),
            left.len() <= i32::MAX,
            forall|j: int| 0 <= j < left.len() as int ==> 1 <= #[trigger] left[j] <= right[j],
        ensures
            res as int == Self::spec_overlap_count(start as int, d as int, left@, right@),
            0 <= res <= left.len() as i32,
    {
        let mut cnt: i32 = 0;
        let mut j: usize = 0;
        while j < left.len() {
            if Self::overlaps_window(start, d, left[j], right[j]) {
                cnt = cnt + 1;
            }
            j = j + 1;
        }
        cnt
    }

    pub fn best_start_days(n: i32, d: i32, left: Vec<i32>, right: Vec<i32>) -> (res: (i32, i32))
        requires
            1 <= n,
            n <= 100000,
            1 <= d <= n,
            1 <= left.len() <= n as nat,
            left.len() == right.len(),
            forall|j: int| 0 <= j < left.len() as int ==> 1 <= #[trigger] left[j] <= right[j] <= n,
        ensures
            1 <= res.0 <= n - d + 1,
            1 <= res.1 <= n - d + 1,
            forall|s: int|
                1 <= s <= n as int - d as int + 1
                    ==> Self::spec_overlap_count(res.0 as int, d as int, left@, right@)
                        >= #[trigger] Self::spec_overlap_count(s, d as int, left@, right@),
            forall|s: int|
                1 <= s <= n as int - d as int + 1
                    ==> Self::spec_overlap_count(res.1 as int, d as int, left@, right@)
                        <= #[trigger] Self::spec_overlap_count(s, d as int, left@, right@),
            forall|s: int|
                1 <= s <= n as int - d as int + 1
                    && #[trigger] Self::spec_overlap_count(s, d as int, left@, right@)
                        == Self::spec_overlap_count(res.0 as int, d as int, left@, right@)
                    ==> res.0 as int <= s,
            forall|s: int|
                1 <= s <= n as int - d as int + 1
                    && #[trigger] Self::spec_overlap_count(s, d as int, left@, right@)
                        == Self::spec_overlap_count(res.1 as int, d as int, left@, right@)
                    ==> res.1 as int <= s,
    {
        let m = n - d + 1;

        let mm = m as usize;
        let mut diff: Vec<i32> = Vec::with_capacity(mm + 2);
        let mut p: usize = 0;
        while p < mm + 2 {
            diff.push(0);
            p += 1;
        }

        let mut j: usize = 0;
        while j < left.len() {
            let l = left[j];
            let r = right[j];
            let lo = if l - d + 1 > 1 { l - d + 1 } else { 1 };
            let hi = if r < m { r } else { m };
            if lo <= hi {
                let li = lo as usize;
                let hi1 = (hi + 1) as usize;
                diff[li] += 1;
                diff[hi1] -= 1;
            }
            j += 1;
        }

        let mut best_bro: i32 = 1;
        let mut best_mom: i32 = 1;
        let mut best_bro_count: i32 = i32::MIN;
        let mut best_mom_count: i32 = i32::MAX;

        let mut cur: i32 = 0;
        let mut start: usize = 1;
        while start <= mm {
            cur += diff[start];
            if cur > best_bro_count {
                best_bro_count = cur;
                best_bro = start as i32;
            }
            if cur < best_mom_count {
                best_mom_count = cur;
                best_mom = start as i32;
            }
            start += 1;
        }

        (best_bro, best_mom)
    }
}

}
