use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn sorted_asc(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
}

pub open spec fn merge_seq(a: Seq<int>, b: Seq<int>) -> Seq<int>
    decreases a.len() + b.len()
{
    if a.len() == 0 {
        b
    } else if b.len() == 0 {
        a
    } else if a[0] <= b[0] {
        seq![a[0]] + merge_seq(a.drop_first(), b)
    } else {
        seq![b[0]] + merge_seq(a, b.drop_first())
    }
}

pub open spec fn merge_sort_seq(s: Seq<int>) -> Seq<int>
    decreases s.len()
{
    if s.len() <= 1 {
        s
    } else {
        let mid = s.len() as int / 2;
        merge_seq(merge_sort_seq(s.subrange(0, mid)), merge_sort_seq(s.subrange(mid, s.len() as int)))
    }
}

pub struct Solution;

impl Solution {
    pub open spec fn min_box_upto(boxes_j: Seq<i32>, pkg: i32, end: int) -> int
        decreases end
    {
        if end <= 0 {
            -1
        } else {
            let prev = Self::min_box_upto(boxes_j, pkg, end - 1);
            let cur = boxes_j[end - 1] as int;
            if cur >= pkg as int {
                if prev == -1 || cur <= prev { cur } else { prev }
            } else {
                prev
            }
        }
    }

    pub open spec fn can_fit_upto(packages: Seq<i32>, boxes_j: Seq<i32>, end: int) -> bool
        decreases end
    {
        if end <= 0 {
            true
        } else {
            Self::can_fit_upto(packages, boxes_j, end - 1)
                && Self::min_box_upto(boxes_j, packages[end - 1], boxes_j.len() as int) >= packages[end - 1] as int
        }
    }

    pub open spec fn waste_upto(packages: Seq<i32>, boxes_j: Seq<i32>, end: int) -> int
        decreases end
    {
        if end <= 0 {
            0
        } else {
            (Self::min_box_upto(boxes_j, packages[end - 1], boxes_j.len() as int) - packages[end - 1] as int)
                + Self::waste_upto(packages, boxes_j, end - 1)
        }
    }

    pub open spec fn total_boxes_len(boxes: Seq<Vec<i32>>, j: int) -> int
        decreases j
    {
        if j <= 0 { 0int } else { Self::total_boxes_len(boxes, j - 1) + boxes[j - 1]@.len() as int }
    }

    pub open spec fn best_waste_upto(packages: Seq<i32>, boxes: Seq<Vec<i32>>, end: int) -> int
        decreases end
    {
        if end <= 0 {
            -1
        } else {
            let prev = Self::best_waste_upto(packages, boxes, end - 1);
            let boxes_j = boxes[end - 1]@;
            let n = packages.len() as int;
            if Self::can_fit_upto(packages, boxes_j, n) {
                let w = Self::waste_upto(packages, boxes_j, n);
                if prev == -1 || w < prev { w } else { prev }
            } else {
                prev
            }
        }
    }
}

pub open spec fn to_int_seq(s: Seq<i32>) -> Seq<int> {
    s.map_values(|x: i32| x as int)
}

fn merge_exec(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires
        sorted_asc(to_int_seq(a@)),
        sorted_asc(to_int_seq(b@)),
    ensures
        to_int_seq(result@) == merge_seq(to_int_seq(a@), to_int_seq(b@)),
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;
    while i < a.len() || j < b.len() {
        if j >= b.len() || (i < a.len() && a[i] <= b[j]) {
            result.push(a[i]);
            i += 1;
        } else {
            result.push(b[j]);
            j += 1;
        }
    }
    result
}

fn merge_sort_exec(v: &Vec<i32>) -> (result: Vec<i32>)
    requires v.len() <= 100_000,
    ensures to_int_seq(result@) == merge_sort_seq(to_int_seq(v@)),
    decreases v.len()
{
    if v.len() <= 1 {
        let mut result: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < v.len() {
            result.push(v[k]);
            k += 1;
        }
        result
    } else {
        let mid = v.len() / 2;
        let mut left: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < mid {
            left.push(v[i]);
            i += 1;
        }
        let mut right: Vec<i32> = Vec::new();
        let mut i2: usize = mid;
        while i2 < v.len() {
            right.push(v[i2]);
            i2 += 1;
        }
        let sorted_left = merge_sort_exec(&left);
        let sorted_right = merge_sort_exec(&right);
        let result = merge_exec(&sorted_left, &sorted_right);
        result
    }
}

impl Solution {
    pub fn min_wasted_space(packages: Vec<i32>, boxes: Vec<Vec<i32>>) -> (res: i32)
        requires
            1 <= packages.len() <= 100_000,
            forall |i: int| 0 <= i < packages.len() ==> 1 <= #[trigger] packages[i] <= 100_000,
            1 <= boxes.len() <= 100_000,
            forall |j: int| #![trigger boxes@[j]] 0 <= j < boxes@.len() ==> 1 <= boxes@[j]@.len() <= 100_000,
            forall |j: int, k: int| 0 <= j < boxes@.len() && 0 <= k < boxes@[j]@.len()
                ==> 1 <= #[trigger] boxes@[j]@[k] <= 100_000,
            1 <= Self::total_boxes_len(boxes@, boxes@.len() as int) <= 100_000,
            forall |j: int, k1: int, k2: int| 0 <= j < boxes@.len() && 0 <= k1 < k2 < boxes@[j]@.len()
                ==> boxes@[j]@[k1] != boxes@[j]@[k2],
        ensures
            Self::best_waste_upto(packages@, boxes@, boxes@.len() as int) == -1 ==> res == -1i32,
            Self::best_waste_upto(packages@, boxes@, boxes@.len() as int) >= 0 ==>
                res == (Self::best_waste_upto(packages@, boxes@, boxes@.len() as int) % 1_000_000_007) as i32,
    {
        let n = packages.len();
        let m = boxes.len();
        let modulo: i64 = 1_000_000_007;

        let mut pkg_count: Vec<i64> = Vec::new();
        let mut vi: usize = 0;
        while vi <= 100_000 {
            pkg_count.push(0);
            vi += 1;
        }

        let mut i: usize = 0;
        while i < n {
            let val = packages[i] as usize;
            pkg_count.set(val, pkg_count[val] + 1);
            i += 1;
        }

        let mut pkg_count_prefix: Vec<i64> = Vec::new();
        pkg_count_prefix.push(pkg_count[0]);
        let mut pkg_sum_prefix: Vec<i64> = Vec::new();
        pkg_sum_prefix.push(0);
        let mut v1: usize = 1;
        while v1 <= 100_000 {
            let next_count = pkg_count_prefix[v1 - 1] + pkg_count[v1];
            pkg_count_prefix.push(next_count);
            let next_sum = pkg_sum_prefix[v1 - 1] + (v1 as i64) * pkg_count[v1];
            pkg_sum_prefix.push(next_sum);
            v1 += 1;
        }

        let mut best: i64 = -1;
        let mut j: usize = 0;
        while j < m {
            let sorted_bj = merge_sort_exec(&boxes[j]);
            let bj_len = sorted_bj.len();
            let mut waste: i64 = 0;
            let mut prev: usize = 0;
            let mut t: usize = 0;
            while t < bj_len {
                let b = sorted_bj[t];
                let bu = b as usize;
                let cnt = pkg_count_prefix[bu] - pkg_count_prefix[prev];
                let sm = pkg_sum_prefix[bu] - pkg_sum_prefix[prev];
                waste = waste + (bu as i64) * cnt - sm;
                prev = bu;
                t += 1;
            }
            let remaining = pkg_count_prefix[100_000] - pkg_count_prefix[prev];
            let can_fit = remaining == 0;
            if can_fit {
                if best == -1 || waste < best {
                    best = waste;
                }
            }
            j += 1;
        }

        if best == -1 {
            -1
        } else {
            (best % modulo) as i32
        }
    }
}

}
