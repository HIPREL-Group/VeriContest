use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sorted_between(a: Seq<i32>, from: int, to: int) -> bool {
        forall |i: int, j: int| from <= i < j < to ==> a[i] <= a[j]
    }

    pub open spec fn is_reorder_of<T>(r: Seq<int>, p: Seq<T>, s: Seq<T>) -> bool {
        &&& r.len() == s.len()
        &&& p.len() == s.len()
        &&& forall|i: int| 0 <= i < r.len() ==> 0 <= #[trigger] r[i] < r.len()
        &&& forall|i: int, j: int| 0 <= i < j < r.len() ==> r[i] != r[j]
        &&& p =~= r.map_values(|i: int| s[i])
    }

    pub open spec fn op_cost_at(v: int, idx: int, mid: int, k: int) -> int {
        if idx < mid {
            if v > k { v - k } else { 0 }
        } else if idx == mid {
            if v >= k { v - k } else { k - v }
        } else {
            if v < k { k - v } else { 0 }
        }
    }

    pub open spec fn cost_prefix(s: Seq<i32>, k: int, mid: int, n: int) -> int
        decreases n,
    {
        if n <= 0 {
            0
        } else if n > s.len() {
            Self::cost_prefix(s, k, mid, s.len() as int)
        } else {
            Self::cost_prefix(s, k, mid, n - 1)
                + Self::op_cost_at(s[n - 1] as int, n - 1, mid, k)
        }
    }

    pub open spec fn cost_all(s: Seq<i32>, k: int) -> int {
        Self::cost_prefix(s, k, (s.len() / 2) as int, s.len() as int)
    }
}

pub open spec fn encode(v: int, i: int) -> int {
    v * 200000 + i
}

pub open spec fn decode_val(e: int) -> int {
    e / 200000
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

pub open spec fn to_int_seq64(s: Seq<i64>) -> Seq<int> {
    s.map_values(|x: i64| x as int)
}

fn merge_exec(a: &Vec<i64>, b: &Vec<i64>) -> (result: Vec<i64>)
    requires
        sorted_asc(to_int_seq64(a@)),
        sorted_asc(to_int_seq64(b@)),
    ensures
        to_int_seq64(result@) == merge_seq(to_int_seq64(a@), to_int_seq64(b@)),
{
    let mut result: Vec<i64> = Vec::new();
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

fn merge_sort_exec(v: &Vec<i64>) -> (result: Vec<i64>)
    requires v.len() <= 200_000,
    ensures to_int_seq64(result@) == merge_sort_seq(to_int_seq64(v@)),
    decreases v.len()
{
    if v.len() <= 1 {
        let mut result: Vec<i64> = Vec::new();
        let mut k: usize = 0;
        while k < v.len() {
            result.push(v[k]);
            k += 1;
        }
        result
    } else {
        let mid = v.len() / 2;
        let mut left: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < mid {
            left.push(v[i]);
            i += 1;
        }
        let mut right: Vec<i64> = Vec::new();
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

fn encode_exec(v: i32, i: usize) -> (result: i64)
    requires 1 <= v <= 1_000_000_000, i < 200000,
    ensures result as int == encode(v as int, i as int),
{
    (v as i64) * 200000 + (i as i64)
}

fn decode_val_exec(e: i64) -> (result: i64)
    requires 0 <= e <= 1_000_000_000i64 * 200000i64 + 199999i64,
    ensures result as int == decode_val(e as int),
{
    e / 200000
}

impl Solution {
    pub fn min_operations_to_make_median_k(nums: Vec<i32>, k: i32) -> (result: i64)
        requires
            1 <= nums.len() <= 200000,
            1 <= k <= 1000000000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000000000,
        ensures
            exists|s: Seq<i32>, r: Seq<int>|
                Self::sorted_between(s, 0, s.len() as int)
                && Self::is_reorder_of(r, s, nums@)
                && result as int == Self::cost_all(s, k as int),
    {
        let n = nums.len();

        let mut enc: Vec<i64> = Vec::new();
        let mut ii: usize = 0;
        while ii < n {
            let e = encode_exec(nums[ii], ii);
            enc.push(e);
            ii += 1;
        }

        let sorted = merge_sort_exec(&enc);

        let mut a: Vec<i32> = Vec::new();
        let mut pp: usize = 0;
        while pp < n {
            let dv = decode_val_exec(sorted[pp]);
            let v32 = dv as i32;
            a.push(v32);
            pp += 1;
        }

        let mid = n / 2;
        let mut ans: i128 = 0;
        let mut idx: usize = 0;
        while idx < n {
            let v = a[idx];
            if idx < mid {
                if v > k {
                    let d = v - k;
                    ans = ans + d as i128;
                }
            } else if idx == mid {
                if v >= k {
                    let d = v - k;
                    ans = ans + d as i128;
                } else {
                    let d = k - v;
                    ans = ans + d as i128;
                }
            } else {
                if v < k {
                    let d = k - v;
                    ans = ans + d as i128;
                }
            }
            idx = idx + 1;
        }

        ans as i64
    }
}

}
