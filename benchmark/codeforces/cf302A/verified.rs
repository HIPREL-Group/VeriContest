use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_ones_seq(seq: Seq<i8>, n: int) -> int
    recommends 0 <= n <= seq.len(),
    decreases n,
{
    if n <= 0 { 0int }
    else {
        let prev = count_ones_seq(seq, n - 1);
        if seq[n - 1] == 1i8 { prev + 1 } else { prev }
    }
}

pub open spec fn query_answer(pos: int, neg: int, l: int, r: int) -> u8 {
    let len = r - l + 1;
    if len % 2 == 0 && len / 2 <= pos && len / 2 <= neg { 1u8 } else { 0u8 }
}

proof fn lemma_count_ones_bounds(seq: Seq<i8>, n: int)
    requires 0 <= n <= seq.len(),
    ensures 0 <= count_ones_seq(seq, n) <= n,
    decreases n,
{
    if n <= 0 {} else { lemma_count_ones_bounds(seq, n - 1); }
}

impl Solution {
    pub fn answer_queries(a: Vec<i8>, qls: Vec<usize>, qrs: Vec<usize>) -> (result: Vec<u8>)
        requires
            1 <= a.len() <= 200000,
            1 <= qls.len() <= 200000,
            qls.len() == qrs.len(),
            forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] == 1i8 || a[i] == -1i8,
            forall|i: int| 0 <= i < qls.len() ==> 1 <= #[trigger] qls[i] <= qrs[i] <= a.len(),
        ensures
            result.len() == qls.len(),
            forall|i: int| 0 <= i < qls.len() ==>
                #[trigger] result[i] == query_answer(
                    count_ones_seq(a@, a.len() as int),
                    a.len() as int - count_ones_seq(a@, a.len() as int),
                    qls[i] as int,
                    qrs[i] as int,
                ),
    {
        let n = a.len();
        let m = qls.len();
        let mut pos: usize = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == a.len(),
                1 <= n <= 200000,
                forall|j: int| 0 <= j < a.len() ==> #[trigger] a[j] == 1i8 || a[j] == -1i8,
                pos as int == count_ones_seq(a@, i as int),
                pos <= i,
            decreases n - i,
        {
            proof {
                lemma_count_ones_bounds(a@, i as int + 1);
            }
            if a[i] == 1i8 {
                pos = pos + 1;
            }
            i = i + 1;
        }
        proof {
            lemma_count_ones_bounds(a@, n as int);
        }
        let total_pos = pos;
        let neg = n - pos;
        let mut out: Vec<u8> = Vec::new();
        let mut k: usize = 0;
        while k < m
            invariant
                0 <= k <= m,
                m == qls.len(),
                m == qrs.len(),
                1 <= m <= 200000,
                1 <= n <= 200000,
                n == a.len(),
                total_pos == pos,
                neg == n - pos,
                pos as int == count_ones_seq(a@, n as int),
                pos <= n,
                out.len() == k,
                forall|j: int| 0 <= j < qls.len() ==> 1 <= #[trigger] qls[j] <= qrs[j] <= a.len(),
                forall|j: int| 0 <= j < k ==>
                    #[trigger] out[j] == query_answer(
                        count_ones_seq(a@, a.len() as int),
                        a.len() as int - count_ones_seq(a@, a.len() as int),
                        qls[j] as int,
                        qrs[j] as int,
                    ),
            decreases m - k,
        {
            let l = qls[k];
            let r = qrs[k];
            let len = r - l + 1;
            let half = len / 2;
            if len % 2 == 0 && half <= pos && half <= neg {
                out.push(1u8);
            } else {
                out.push(0u8);
            }
            k = k + 1;
        }
        out
    }
}

}
