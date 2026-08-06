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
            Self::spec_max2(Self::spec_max_freq_upto(a, upto - 1), Self::spec_count(a, a[upto - 1] as int))
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

    fn merge(left: Vec<i32>, right: Vec<i32>) -> (result: Vec<i32>) {
        let mut result: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        let mut j: usize = 0;
        while i < left.len() && j < right.len() {
            if left[i] <= right[j] {
                let x = left[i];
                result.push(x);
                i += 1;
            } else {
                let x = right[j];
                result.push(x);
                j += 1;
            }
        }
        while i < left.len() {
            let x = left[i];
            result.push(x);
            i += 1;
        }
        while j < right.len() {
            let x = right[j];
            result.push(x);
            j += 1;
        }
        result
    }

    fn merge_sort(a: Vec<i32>) -> (result: Vec<i32>) {
        let n = a.len();
        if n <= 1 {
            a
        } else {
            let mid = n / 2;
            let mut left: Vec<i32> = Vec::new();
            let mut k: usize = 0;
            while k < mid {
                left.push(a[k]);
                k += 1;
            }
            let mut right: Vec<i32> = Vec::new();
            let mut k2: usize = mid;
            while k2 < n {
                right.push(a[k2]);
                k2 += 1;
            }
            let left_sorted = Self::merge_sort(left);
            let right_sorted = Self::merge_sort(right);
            let result = Self::merge(left_sorted, right_sorted);
            result
        }
    }

    fn compute_rank(s: &Vec<i32>) -> (rank: Vec<i32>) {
        let n = s.len();
        let mut rank: Vec<i32> = Vec::new();
        rank.push(1);
        let mut k: usize = 1;
        while k < n {
            let inc: i32 = if s[k] > s[k - 1] { 1 } else { 0 };
            let newval = rank[k - 1] + inc;
            rank.push(newval);
            k += 1;
        }
        rank
    }

    fn find_index(s: &Vec<i32>, x: i32) -> (pos: usize) {
        let mut lo: usize = 0;
        let mut hi: usize = s.len();
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if s[mid] < x {
                lo = mid + 1;
            } else if s[mid] > x {
                hi = mid;
            } else {
                return mid;
            }
        }
        0
    }

    fn compress(a: &Vec<i32>) -> (comp: Vec<i32>) {
        let mut a_copy: Vec<i32> = Vec::new();
        let mut ci: usize = 0;
        while ci < a.len() {
            a_copy.push(a[ci]);
            ci += 1;
        }
        let s = Self::merge_sort(a_copy);
        let rank = Self::compute_rank(&s);
        let n = a.len();
        let mut comp: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            let pos = Self::find_index(&s, a[i]);
            let r = rank[pos];
            comp.push(r);
            i += 1;
        }
        comp
    }

    pub fn min_remaining_after_epic_transformation(a: Vec<i32>) -> (res: i32)
        requires
            1 <= a.len() <= 200000,
            forall|j: int| 0 <= j < a.len() as int ==> 1 <= #[trigger] a[j] <= 1_000_000_000,
        ensures
            res as int == Self::spec_min_remaining(a@),
    {
        let n: usize = a.len();
        let comp = Self::compress(&a);

        let mut cnt: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k <= n {
            cnt.push(0);
            k = k + 1;
        }

        let mut i: usize = 0;
        while i < n {
            let v: usize = comp[i] as usize;
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
