use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {

pub open spec fn is_desc(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < s.len() ==> s[i] >= s[j]
}

pub open spec fn to_int_seq(s: Seq<i32>) -> Seq<int>
    decreases s.len()
{
    if s.len() == 0 { Seq::empty() }
    else { Self::to_int_seq(s.drop_last()).push(s.last() as int) }
}

pub open spec fn insert_desc(s: Seq<int>, v: int) -> Seq<int>
    decreases s.len()
{
    if s.len() == 0 { seq![v] }
    else if v >= s[0] { seq![v].add(s) }
    else { seq![s[0]].add(Self::insert_desc(s.subrange(1, s.len() as int), v)) }
}

pub open spec fn ssort(s: Seq<int>) -> Seq<int>
    decreases s.len()
{
    if s.len() == 0 { Seq::empty() }
    else { Self::insert_desc(Self::ssort(s.drop_last()), s.last()) }
}

pub open spec fn merge_ops_n(s: Seq<int>, k: int, n: nat) -> int
    decreases n
{
    if n == 0 { 0 }
    else if s.len() < 2 { 0 }
    else if s[s.len() - 1] >= k { 0 }
    else {
        1 + Self::merge_ops_n(Self::insert_desc(s.subrange(0, s.len() - 2), 2 * s[s.len() - 1] + s[s.len() - 2]), k, (n - 1) as nat)
    }
}

pub open spec fn merge_ops(s: Seq<int>, k: int) -> int {
    Self::merge_ops_n(s, k, s.len())
}

pub fn min_operations(nums: Vec<i32>, k: i32) -> (res: i32)
    requires
        2 <= nums.len() <= 200_000,
        1 <= k <= 1_000_000_000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
    ensures
        res as int == Self::merge_ops(Self::ssort(Self::to_int_seq(nums@)), k as int),
{
    let mut h: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t < nums.len() {
        let v = nums[t];
        let vi = v as i64;
        let mut p: usize = 0;
        while p < h.len() && h[p] > vi {
            p += 1;
        }
        h.insert(p, vi);
        t += 1;
    }
    let mut ops: i32 = 0;
    while h.len() >= 2 && h[h.len() - 1] < k as i64 {
        let nh = h.len();
        let x = h[nh - 1];
        let y = h[nh - 2];
        let merged = 2 * x + y;
        let _ = h.pop();
        let _ = h.pop();
        let mut p: usize = 0;
        while p < h.len() && h[p] > merged {
            p += 1;
        }
        h.insert(p, merged);
        ops = ops + 1;
    }
    ops
}

}

}
