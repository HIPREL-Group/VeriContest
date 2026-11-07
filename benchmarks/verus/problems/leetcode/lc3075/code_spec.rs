use vstd::prelude::*;
use vstd::relations::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn max_index_prefix(s: Seq<i32>, n: int) -> int
        decreases n,
    {
        if n <= 1 {
            0
        } else {
            let j = Self::max_index_prefix(s, n - 1);
            if s[n - 1] >= s[j] {
                n - 1
            } else {
                j
            }
        }
    }

    pub open spec fn max_value(s: Seq<i32>) -> int {
        if s.len() == 0 {
            -1
        } else {
            s[Self::max_index_prefix(s, s.len() as int)] as int
        }
    }

    pub open spec fn pick_max_mark(s: Seq<i32>) -> Seq<i32> {
        if s.len() == 0 {
            s
        } else {
            s.update(Self::max_index_prefix(s, s.len() as int), -1i32)
        }
    }

    pub open spec fn after_rounds(s: Seq<i32>, rounds: int) -> Seq<i32>
        decreases rounds,
    {
        if rounds <= 0 {
            s
        } else {
            Self::pick_max_mark(Self::after_rounds(s, rounds - 1))
        }
    }

    pub open spec fn clamp_gain(v: int, taken: int) -> int {
        if v - taken > 0 {
            v - taken
        } else {
            0
        }
    }

    pub open spec fn maximum_from_state(s: Seq<i32>, rounds: int, taken: int) -> int
        decreases rounds,
    {
        if rounds <= 0 || s.len() == 0 {
            0
        } else {
            Self::clamp_gain(Self::max_value(s), taken)
                + Self::maximum_from_state(Self::pick_max_mark(s), rounds - 1, taken + 1)
        }
    }

    pub open spec fn maximum_happiness_sum_spec(happiness: Seq<i32>, k: int) -> int {
        Self::maximum_from_state(happiness, k, 0)
    }
}

pub open spec fn desc_leq(a: i32, b: i32) -> bool {
    a >= b
}

pub open spec fn merge_seq_desc(a: Seq<i32>, b: Seq<i32>) -> Seq<i32>
    decreases a.len() + b.len()
{
    if a.len() == 0 {
        b
    } else if b.len() == 0 {
        a
    } else if a[0] >= b[0] {
        seq![a[0]] + merge_seq_desc(a.drop_first(), b)
    } else {
        seq![b[0]] + merge_seq_desc(a, b.drop_first())
    }
}

pub open spec fn merge_sort_seq_desc(s: Seq<i32>) -> Seq<i32>
    decreases s.len()
{
    if s.len() <= 1 {
        s
    } else {
        let mid = s.len() as int / 2;
        merge_seq_desc(merge_sort_seq_desc(s.subrange(0, mid)), merge_sort_seq_desc(s.subrange(mid, s.len() as int)))
    }
}

fn merge_exec_desc(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires
        sorted_by(a@, |x: i32, y: i32| desc_leq(x, y)),
        sorted_by(b@, |x: i32, y: i32| desc_leq(x, y)),
    ensures
        result@ =~= merge_seq_desc(a@, b@),
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;
    while i < a.len() || j < b.len() {
        if j >= b.len() || (i < a.len() && a[i] >= b[j]) {
            result.push(a[i]);
            i += 1;
        } else {
            result.push(b[j]);
            j += 1;
        }
    }
    result
}

fn merge_sort_exec_desc(v: &Vec<i32>) -> (result: Vec<i32>)
    requires v.len() <= 200_000,
    ensures result@ =~= merge_sort_seq_desc(v@),
    decreases v.len()
{
    if v.len() <= 1 {
        v.clone()
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
        let sorted_left = merge_sort_exec_desc(&left);
        let sorted_right = merge_sort_exec_desc(&right);
        let result = merge_exec_desc(&sorted_left, &sorted_right);
        result
    }
}

impl Solution {
    pub fn maximum_happiness_sum(happiness: Vec<i32>, k: i32) -> (result: i64)
        requires
            1 <= happiness.len() <= 200000,
            1 <= k <= happiness.len(),
            forall |i: int| 0 <= i < happiness.len() ==> 1 <= #[trigger] happiness[i] <= 100000000,
        ensures
            result as int == Self::maximum_happiness_sum_spec(happiness@, k as int),
    {
        let sorted = merge_sort_exec_desc(&happiness);
        let mut ans: i64 = 0;
        let mut i: usize = 0;
        let ku = k as usize;
        while i < ku {
            let v = sorted[i] as i64;
            let gain = v - i as i64;
            if gain > 0 {
                ans = ans + gain;
            }
            i += 1;
        }
        ans
    }
}

}
