use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn non_decreasing(seq: Seq<i64>, lo: int, hi: int) -> bool
    recommends lo <= hi,
{
    forall|i: int| lo <= i && i < hi ==> #[trigger] seq[i] <= seq[i + 1]
}

pub open spec fn non_increasing(seq: Seq<i64>, lo: int, hi: int) -> bool
    recommends lo <= hi,
{
    forall|i: int| lo <= i && i < hi ==> #[trigger] seq[i] >= seq[i + 1]
}

pub open spec fn is_ladder(seq: Seq<i64>, l: int, r: int) -> bool
    recommends 0 <= l && l <= r && r < seq.len(),
{
    exists|k: int|
        l <= k && k <= r && non_decreasing(seq, l, k) && non_increasing(seq, k, r)
}

pub open spec fn up_end_spec(seq: Seq<i64>, i: int) -> int
    recommends 0 <= i && i < seq.len(),
    decreases (seq.len() - 1 - i) as nat,
{
    if i + 1 >= seq.len() {
        i
    } else if seq[i] <= seq[i + 1] {
        up_end_spec(seq, i + 1)
    } else {
        i
    }
}

pub open spec fn down_end_spec(seq: Seq<i64>, i: int) -> int
    recommends 0 <= i && i < seq.len(),
    decreases (seq.len() - 1 - i) as nat,
{
    if i + 1 >= seq.len() {
        i
    } else if seq[i] >= seq[i + 1] {
        down_end_spec(seq, i + 1)
    } else {
        i
    }
}

pub open spec fn ladder_end_spec(seq: Seq<i64>, l: int) -> int
    recommends 0 <= l && l < seq.len(),
{
    down_end_spec(seq, up_end_spec(seq, l))
}

impl Solution {
    pub fn query_ladders(arr: Vec<i64>, queries: Vec<(i32, i32)>) -> (res: Vec<bool>)
        requires
            1 <= arr.len() <= 100_000,
            1 <= queries.len() <= 100_000,
            forall|i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 1_000_000_000,
            forall|q: int|
                0 <= q < queries.len() ==> {
                    let (l1, r1) = #[trigger] queries[q];
                    1 <= l1 && l1 <= r1 && (r1 as int) <= arr.len()
                },
        ensures
            res.len() == queries.len(),
            forall|k: int|
                0 <= k && k < res.len() ==> (#[trigger] res[k] == is_ladder(arr@, (queries[k].0 as int) - 1, (queries[k].1 as int) - 1)),
    {
        let n = arr.len();
        let mut up_end = Vec::new();
        let mut i = 0usize;
        while i < n
            decreases n - i,
        {
            up_end.push(0usize);
            i = i + 1;
        }
        up_end.set(n - 1, n - 1);
        i = n - 1;
        while i > 0
            decreases i,
        {
            let j = i - 1;
            if arr[j] <= arr[j + 1] {
                up_end.set(j, up_end[j + 1]);
            } else {
                up_end.set(j, j);
            }
            i = j;
        }
        let mut down_end = Vec::new();
        i = 0;
        while i < n
            decreases n - i,
        {
            down_end.push(0usize);
            i = i + 1;
        }
        down_end.set(n - 1, n - 1);
        i = n - 1;
        while i > 0
            decreases i,
        {
            let j = i - 1;
            if arr[j] >= arr[j + 1] {
                down_end.set(j, down_end[j + 1]);
            } else {
                down_end.set(j, j);
            }
            i = j;
        }
        let mut res = Vec::new();
        let mut qi = 0usize;
        while qi < queries.len()
            decreases queries.len() - qi,
        {
            let (l1, r1) = queries[qi];
            let l = (l1 - 1) as usize;
            let r = (r1 - 1) as usize;
            let peak = up_end[l];
            let answer = down_end[peak] >= r;
            res.push(answer);
            qi = qi + 1;
        }
        res
    }
}

}
