use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn spec_sum(a: Seq<i32>, n: int) -> int
    decreases n,
{
    if n <= 0 {
        0
    } else {
        spec_sum(a, n - 1) + a[n - 1] as int
    }
}

pub open spec fn spec_count_eq(a: Seq<i32>, n: int, v: int) -> int
    decreases n,
{
    if n <= 0 {
        0
    } else {
        spec_count_eq(a, n - 1, v) + (if a[n - 1] as int == v {
            1int
        } else {
            0int
        })
    }
}

pub open spec fn is_nice(a: Seq<i32>, n: int, j: int) -> bool {
    0 <= j && j < n && (
        {
            let s = spec_sum(a, n);
            let t = s - a[j] as int;
            t % 2 == 0 && {
                let need = t / 2;
                let cnt = spec_count_eq(a, n, need);
                (a[j] as int == need && cnt >= 2) || (a[j] as int != need && cnt >= 1)
            }
        }
    )
}

pub open spec fn output_has_index(res: Seq<i32>, jb: int) -> bool {
    res.contains(jb as i32)
}

pub open spec fn res_indices_pairwise_distinct(res: Seq<i32>) -> bool {
    forall|i: int, k: int|
        0 <= i && i < k && k < res.len() as int
        ==> #[trigger] res[i] != #[trigger] res[k]
}

pub struct Solution;

impl Solution {
    pub fn nice_indices(n: usize, a: Vec<i32>) -> (res: Vec<i32>)
        requires
            2 <= n && n <= 200_000,
            a.len() == n,
            forall|i: int| 0 <= i && i < n ==> 1 <= #[trigger] a@[i] && a@[i] <= 1_000_000,
        ensures
            forall|jb: int| 1 <= jb && jb <= n as int ==> (
                is_nice(a@, n as int, jb - 1) <==> output_has_index(res@, jb)
            ),
            forall|t: int| 0 <= t && t < res.len() ==> 1 <= #[trigger] res[t] && res[t] <= n as int,
            res_indices_pairwise_distinct(res@),
    {
        let mut freq: Vec<i32> = Vec::new();
        let mut fi: usize = 0;
        while fi < 1_000_000 + 1 {
            freq.push(0i32);
            fi += 1;
        }
        let mut s: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            let v = a[i] as usize;
            freq[v] = freq[v] + 1;
            s = s + a[i] as i64;
            i += 1;
        }
        let mut res: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n {
            let aj = a[j] as i64;
            let t = s - aj;
            if t % 2 == 0 {
                let need = t / 2;
                if need >= 1 && need <= 1_000_000 as i64 {
                    let need_u = need as usize;
                    let c = freq[need_u];
                    if aj == need {
                        if c >= 2 {
                            res.push((j + 1) as i32);
                        }
                    } else {
                        if c >= 1 {
                            res.push((j + 1) as i32);
                        }
                    }
                }
            }
            j += 1;
        }
        res
    }
}

}
