use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn halving_steps(d: int) -> int
    decreases d
{
    if d <= 0 { 0 } else { 1 + halving_steps(d / 2) }
}

pub open spec fn is_min_max_of(a: Seq<i64>, mn: int, mx: int) -> bool {
    a.len() >= 1
    && (forall|i: int| 0 <= i < a.len() ==> mn <= #[trigger] (a[i] as int) <= mx)
    && (exists|i: int| 0 <= i < a.len() && a[i] as int == mn)
    && (exists|i: int| 0 <= i < a.len() && a[i] as int == mx)
}

pub struct Solution;

impl Solution {
    pub fn steps_from_diff(d: i64) -> (res: i64)
        requires
            d >= 0,
        ensures
            res >= 0,
            res <= d,
            res as int == halving_steps(d as int),
    {
        if d == 0 {
            0
        } else {
            let sub = Self::steps_from_diff(d / 2);
            sub + 1
        }
    }

    pub fn min_operations(a: Vec<i64>) -> (result: i64)
        requires
            1 <= a.len() <= 200_000,
            forall|i: int| 0 <= i < a.len() ==> 0 <= #[trigger] a[i] <= 1_000_000_000,
        ensures
            result >= 0,
            exists|mn: int, mx: int|
                is_min_max_of(a@, mn, mx)
                && result as int == halving_steps(mx - mn),
    {
        let n = a.len();
        let mut mn = a[0];
        let mut mx = a[0];
        let mut i: usize = 1;
        while i < n {
            let cur = a[i];
            if cur < mn {
                mn = cur;
            }
            if cur > mx {
                mx = cur;
            }
            i += 1;
        }
        Self::steps_from_diff(mx - mn)
    }

    pub open spec fn apply_x_i64(v: i64, x: i64) -> i64 {
        ((v as int + x as int) / 2) as i64
    }

    pub open spec fn apply_x_seq(a: Seq<i64>, ops: Seq<i64>) -> Seq<i64>
        decreases ops.len(),
    {
        if ops.len() == 0 {
            a
        } else {
            let prev = Self::apply_x_seq(a, ops.drop_last());
            Seq::new(prev.len(), |i: int| Self::apply_x_i64(prev[i], ops.last()))
        }
    }

    pub open spec fn all_equal(a: Seq<i64>) -> bool {
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] == a[j]
    }

    pub open spec fn spec_seq_min(a: Seq<i64>) -> i64
        decreases a.len(),
    {
        if a.len() <= 1 {
            a[0]
        } else {
            let sub = Self::spec_seq_min(a.drop_last());
            if a.last() < sub { a.last() } else { sub }
        }
    }

    pub open spec fn spec_seq_max(a: Seq<i64>) -> i64
        decreases a.len(),
    {
        if a.len() <= 1 {
            a[0]
        } else {
            let sub = Self::spec_seq_max(a.drop_last());
            if a.last() > sub { a.last() } else { sub }
        }
    }

    pub fn build_operations(a: Vec<i64>) -> (result: Vec<i64>)
        requires
            1 <= a.len() <= 200_000,
            forall|i: int| 0 <= i < a.len() ==> 0 <= #[trigger] a[i] <= 1_000_000_000,
        ensures
            result.len() as int
                == halving_steps(Self::spec_seq_max(a@) as int - Self::spec_seq_min(a@) as int),
            forall|k: int| 0 <= k < result.len() ==>
                0 <= #[trigger] result[k] <= 1_000_000_000_000_000_000,
            Self::all_equal(Self::apply_x_seq(a@, result@)),
    {
        let n = a.len();
        let mut mn = a[0];
        let mut mx = a[0];
        let mut idx: usize = 1;
        while idx < n {
            let cur = a[idx];
            if cur < mn {
                mn = cur;
            }
            if cur > mx {
                mx = cur;
            }
            idx += 1;
        }
        let steps = Self::steps_from_diff(mx - mn);
        let mut ops: Vec<i64> = Vec::new();
        let mut t: i64 = 0;
        while t < steps {
            let x = if mn % 2 == 1 && mx % 2 == 0 { 1 } else { 0 };
            ops.push(x);
            mn = (mn + x) / 2;
            mx = (mx + x) / 2;
            t += 1;
        }
        ops
    }
}

}
