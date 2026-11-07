use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn inside(points: Seq<Seq<int>>, i: int, j: int, t: int) -> bool {
        &&& points[i][0] <= points[t][0]
        &&& points[t][0] <= points[j][0]
        &&& points[j][1] <= points[t][1]
        &&& points[t][1] <= points[i][1]
    }

    pub open spec fn valid_pair(points: Seq<Seq<int>>, i: int, j: int) -> bool {
        &&& i != j
        &&& points[i][0] <= points[j][0]
        &&& points[i][1] >= points[j][1]
        &&& (forall|t: int|
            0 <= t < points.len() && t != i && t != j ==> !Self::inside(points, i, j, t))
    }

    pub open spec fn count_j(points: Seq<Seq<int>>, i: int, jend: int) -> int
        decreases jend,
    {
        if jend <= 0 {
            0
        } else {
            Self::count_j(points, i, jend - 1) + (if Self::valid_pair(points, i, jend - 1) {
                1int
            } else {
                0int
            })
        }
    }

    pub open spec fn count_i(points: Seq<Seq<int>>, iend: int) -> int
        decreases iend,
    {
        if iend <= 0 {
            0
        } else {
            Self::count_i(points, iend - 1) + Self::count_j(points, iend - 1, points.len() as int)
        }
    }

    pub open spec fn spec_number_of_pairs(points: Seq<Seq<int>>) -> int {
        Self::count_i(points, points.len() as int)
    }
}

pub open spec fn sorted_asc(s: Seq<int>) -> bool {
    forall|a: int, b: int| 0 <= a <= b < s.len() ==> s[a] <= s[b]
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

pub open spec fn encode(x: int, y: int) -> int {
    (x + 1_000_000_000) * 2_000_000_003 + (1_000_000_000 - y)
}

pub open spec fn decode_y(e: int) -> int {
    1_000_000_000 - (e % 2_000_000_003)
}

pub open spec fn to_int_seq64(s: Seq<i64>) -> Seq<int> {
    s.map_values(|x: i64| x as int)
}

fn merge_sort_exec(v: &Vec<i64>) -> (result: Vec<i64>)
    requires v.len() <= 1_000,
    ensures to_int_seq64(result@) == merge_sort_seq(to_int_seq64(v@)),
{
    let n = v.len();
    let mut a: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < n {
        a.push(v[k]);
        k += 1;
    }
    let mut b: Vec<i64> = Vec::new();
    k = 0;
    while k < n {
        b.push(0i64);
        k += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut lo: usize = 0;
        while lo < n {
            let mid: usize = if lo + width < n { lo + width } else { n };
            let hi: usize = if lo + 2 * width < n { lo + 2 * width } else { n };
            let mut i: usize = lo;
            let mut j: usize = mid;
            let mut k2: usize = lo;
            while k2 < hi {
                if j >= hi || (i < mid && a[i] <= a[j]) {
                    b.set(k2, a[i]);
                    i += 1;
                } else {
                    b.set(k2, a[j]);
                    j += 1;
                }
                k2 += 1;
            }
            lo = hi;
        }
        let tmp = a;
        a = b;
        b = tmp;
        width = width * 2;
    }
    a
}

fn encode_exec(x: i32, y: i32) -> (result: i64)
    requires -1_000_000_000 <= x <= 1_000_000_000, -1_000_000_000 <= y <= 1_000_000_000,
    ensures result as int == encode(x as int, y as int),
{
    (x as i64 + 1_000_000_000) * 2_000_000_003 + (1_000_000_000 - y as i64)
}

fn decode_y_exec(e: i64) -> (result: i64)
    requires 0 <= e <= 5_000_000_000_000_000_000i64,
    ensures result as int == decode_y(e as int),
{
    1_000_000_000 - (e % 2_000_000_003)
}

impl Solution {
    pub fn number_of_pairs(points: Vec<Vec<i32>>) -> (result: i32)
        requires
            2 <= points.len() <= 1000,
            forall |i: int| 0 <= i < points.len() ==> #[trigger] points[i].len() == 2,
            forall |i: int| 0 <= i < points.len()
                ==> -1_000_000_000 <= #[trigger] points[i][0] <= 1_000_000_000
                    && -1_000_000_000 <= points[i][1] <= 1_000_000_000,
            forall |i: int, j: int| 0 <= i < j < points.len() ==> #[trigger] points[i] != #[trigger] points[j],
        ensures
            result as int == Self::spec_number_of_pairs(points@.map_values(|p: Vec<i32>| p@.map_values(|v: i32| v as int))),
    {
        let n = points.len();
        let mut total: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            let xi = points[i][0];
            let yi = points[i][1];
            let mut cand: Vec<i64> = Vec::new();
            let mut t: usize = 0;
            while t < n {
                if t != i && xi <= points[t][0] && points[t][1] <= yi {
                    let e = encode_exec(points[t][0], points[t][1]);
                    cand.push(e);
                }
                t += 1;
            }
            let sorted_cand = merge_sort_exec(&cand);
            let m = sorted_cand.len();
            let mut prev_y: i64 = -2_000_000_001;
            let mut cnt: i64 = 0;
            let mut idx: usize = 0;
            while idx < m {
                let y = decode_y_exec(sorted_cand[idx]);
                let has_next_dup = idx + 1 < m && sorted_cand[idx + 1] == sorted_cand[idx];
                let counted = y > prev_y && !has_next_dup;
                if y > prev_y {
                    prev_y = y;
                }
                if counted {
                    cnt += 1;
                }
                idx += 1;
            }
            total = total + cnt;
            i += 1;
        }
        total as i32
    }
}

}
