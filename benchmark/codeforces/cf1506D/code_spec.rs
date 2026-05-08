use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_count_prefix(a: Seq<i32>, v: int, i: int) -> int
        decreases i
    {
        if i <= 0 {
            0
        } else {
            Self::spec_count_prefix(a, v, i - 1) + if a[i - 1] as int == v { 1int } else { 0int }
        }
    }

    pub open spec fn spec_count(a: Seq<i32>, v: int) -> int {
        Self::spec_count_prefix(a, v, a.len() as int)
    }

    pub open spec fn spec_max2(x: int, y: int) -> int {
        if x >= y { x } else { y }
    }

    pub open spec fn spec_max_freq_upto(a: Seq<i32>, upto: int) -> int
        decreases upto
    {
        if upto <= 0 {
            0
        } else {
            Self::spec_max2(Self::spec_max_freq_upto(a, upto - 1), Self::spec_count(a, upto))
        }
    }

    pub open spec fn spec_max_freq(a: Seq<i32>) -> int {
        Self::spec_max_freq_upto(a, a.len() as int)
    }

    pub open spec fn spec_min_remaining(a: Seq<i32>) -> int {
        let n = a.len() as int;
        let m = Self::spec_max_freq(a);
        if 2 * m > n { 2 * m - n } else { n % 2 }
    }

    pub fn min_remaining_after_epic_transformation(a: Vec<i32>) -> (res: i32)
        requires
            1 <= a.len() <= 200000,
            forall|j: int| 0 <= j < a.len() as int ==> 1 <= #[trigger] a[j] <= a.len(),
        ensures
            res as int == Self::spec_min_remaining(a@),
    {
        let n: usize = a.len();
        let mut cnt: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k <= n {
            cnt.push(0);
            k = k + 1;
        }

        let mut i: usize = 0;
        while i < n {
            let v: usize = a[i] as usize;
            cnt.set(v, cnt[v] + 1);
            i = i + 1;
        }

        let mut mx: i32 = 0;
        let mut p: usize = 1;
        while p <= n {
            if cnt[p] > mx {
                mx = cnt[p];
            }
            p = p + 1;
        }

        let n_i32: i32 = n as i32;
        let two_mx: i32 = mx + mx;
        if two_mx > n_i32 {
            two_mx - n_i32
        } else {
            n_i32 % 2
        }
    }
}

}
