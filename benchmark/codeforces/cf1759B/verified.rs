use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn sum_seq(s: Seq<u32>) -> int
    decreases s.len(),
{
    if s.len() == 0 { 0int } else { s[0] as int + sum_seq(s.subrange(1, s.len() as int)) }
}

pub open spec fn max_seq(s: Seq<u32>) -> u32
    decreases s.len(),
{
    if s.len() == 0 { 0u32 }
    else if s.len() == 1 { s[0] }
    else {
        let rest = max_seq(s.subrange(1, s.len() as int));
        if s[0] > rest { s[0] } else { rest }
    }
}

pub open spec fn sum_prefix(s: Seq<u32>, k: int) -> int
    recommends 0 <= k <= s.len(),
    decreases k,
{
    if k <= 0 { 0int } else { s[k - 1] as int + sum_prefix(s, k - 1) }
}

pub open spec fn max_prefix(s: Seq<u32>, k: int) -> u32
    recommends 0 <= k <= s.len(),
    decreases k,
{
    if k <= 0 { 0u32 }
    else {
        let prev = max_prefix(s, k - 1);
        if s[k - 1] > prev { s[k - 1] } else { prev }
    }
}

proof fn lemma_sum_prefix_full(s: Seq<u32>)
    ensures sum_prefix(s, s.len() as int) == sum_seq(s),
    decreases s.len(),
{
    lemma_sum_prefix_eq_seq_at(s, s.len() as int);
    assert(s.subrange(0, s.len() as int) =~= s);
}

proof fn lemma_sum_prefix_eq_seq_at(s: Seq<u32>, k: int)
    requires 0 <= k <= s.len(),
    ensures sum_prefix(s, k) == sum_seq(s.subrange(0, k)),
    decreases k,
{
    if k <= 0 {
        assert(s.subrange(0, 0).len() == 0);
    } else {
        lemma_sum_prefix_eq_seq_at(s, k - 1);
        
        
        lemma_sum_seq_extend(s, k);
    }
}

proof fn lemma_sum_seq_extend(s: Seq<u32>, k: int)
    requires 1 <= k <= s.len(),
    ensures sum_seq(s.subrange(0, k)) == sum_seq(s.subrange(0, k - 1)) + s[k - 1] as int,
    decreases k,
{
    let sub_k = s.subrange(0, k);
    let sub_km1 = s.subrange(0, k - 1);
    if k == 1 {
        assert(sub_k.len() == 1);
        assert(sub_k[0] == s[0]);
        assert(sub_k.subrange(1, 1).len() == 0);
        assert(sum_seq(sub_k.subrange(1, 1)) == 0);
        assert(sum_seq(sub_k) == s[0] as int);
        assert(sub_km1.len() == 0);
        assert(sum_seq(sub_km1) == 0);
    } else {
        
        
        
        let sub_k_tail = sub_k.subrange(1, k);
        let sub_km1_tail = sub_km1.subrange(1, k - 1);
        assert(sub_k_tail =~= s.subrange(1, k));
        assert(sub_km1_tail =~= s.subrange(1, k - 1));
        
        let s_tail = s.subrange(1, s.len() as int);
        
        
        lemma_sum_seq_extend(s_tail, k - 1);
        
        
        assert(s_tail.subrange(0, k - 1) =~= s.subrange(1, k));
        assert(s_tail.subrange(0, k - 2) =~= s.subrange(1, k - 1));
        assert(s_tail[k - 2] == s[k - 1]);
    }
}

proof fn lemma_max_prefix_full(s: Seq<u32>)
    ensures max_prefix(s, s.len() as int) == max_seq(s),
    decreases s.len(),
{
    lemma_max_prefix_eq_seq_at(s, s.len() as int);
    assert(s.subrange(0, s.len() as int) =~= s);
}

proof fn lemma_max_prefix_eq_seq_at(s: Seq<u32>, k: int)
    requires 0 <= k <= s.len(),
    ensures max_prefix(s, k) == max_seq(s.subrange(0, k)),
    decreases k,
{
    if k <= 0 {
        assert(s.subrange(0, 0).len() == 0);
    } else {
        lemma_max_prefix_eq_seq_at(s, k - 1);
        lemma_max_seq_extend(s, k);
    }
}

proof fn lemma_max_seq_extend(s: Seq<u32>, k: int)
    requires 1 <= k <= s.len(),
    ensures max_seq(s.subrange(0, k)) == (
        if s[k - 1] > max_seq(s.subrange(0, k - 1)) { s[k - 1] } else { max_seq(s.subrange(0, k - 1)) }
    ),
    decreases k,
{
    let sub_k = s.subrange(0, k);
    let sub_km1 = s.subrange(0, k - 1);
    if k == 1 {
        assert(sub_k.len() == 1);
        assert(sub_k[0] == s[0]);
        assert(max_seq(sub_k) == s[0]);
        assert(sub_km1.len() == 0);
        assert(max_seq(sub_km1) == 0u32);
        assert(s[0] > 0u32 || s[0] == 0u32);
    } else {
        let s_tail = s.subrange(1, s.len() as int);
        lemma_max_seq_extend(s_tail, k - 1);
        assert(s_tail.subrange(0, k - 1) =~= s.subrange(1, k));
        assert(s_tail.subrange(0, k - 2) =~= s.subrange(1, k - 1));
        assert(s_tail[k - 2] == s[k - 1]);
        
        let sub_k_tail = sub_k.subrange(1, k);
        let sub_km1_tail = sub_km1.subrange(1, k - 1);
        assert(sub_k_tail =~= s.subrange(1, k));
        assert(sub_km1_tail =~= s.subrange(1, k - 1));
    }
}

impl Solution {
    pub fn lost_permutation(b: Vec<u32>, m: usize, s: u32) -> (result: bool)
        requires
            1 <= m <= 50,
            1 <= s <= 1000,
            b.len() == m,
            forall|i: int| 0 <= i < b.len() ==> 1 <= #[trigger] b[i] <= 50,
            forall|i: int, j: int| 0 <= i < j < b.len() ==> b[i] != b[j],
        ensures
            result == (
                exists|n: int| max_seq(b@) <= n <= 100 && #[trigger] (n * (n + 1) / 2) == sum_seq(b@) + s as int
            ),
    {
        let mut sum_b: u32 = 0;
        let mut max_b: u32 = 0;
        let mut i: usize = 0;
        while i < m
            invariant
                1 <= m <= 50,
                b.len() == m,
                forall|k: int| 0 <= k < b.len() ==> 1 <= #[trigger] b[k] <= 50,
                0 <= i <= m,
                sum_b as int == sum_prefix(b@, i as int),
                max_b == max_prefix(b@, i as int),
                sum_b <= 50u32 * (i as u32),
                max_b <= 50u32,
            decreases m - i,
        {
            sum_b += b[i];
            if b[i] > max_b {
                max_b = b[i];
            }
            i += 1;
            proof {
                
            }
        }
        proof {
            lemma_sum_prefix_full(b@);
            lemma_max_prefix_full(b@);
            assert(b@.subrange(0, b.len() as int) =~= b@);
            assert(sum_b as int == sum_seq(b@));
            assert(max_b == max_seq(b@));
        }
        let target: u32 = sum_b + s;
        let mut n: u32 = max_b;
        let mut found: bool = false;
        while n <= 100
            invariant
                target as int == sum_seq(b@) + s as int,
                max_b == max_seq(b@),
                max_b >= 1,
                max_b <= n <= 101,
                target <= 3500,
                found == (exists|nn: int| max_seq(b@) <= nn < n as int && #[trigger] (nn * (nn + 1) / 2) == sum_seq(b@) + s as int),
            decreases 102 - n as int,
        {
            let n64: u64 = n as u64;
            assert(n64 <= 100);
            assert(n64 * (n64 + 1) <= 100u64 * 101u64) by (nonlinear_arith)
                requires n64 <= 100;
            let prod: u64 = n64 * (n64 + 1);
            if prod / 2 == target as u64 {
                found = true;
                proof {
                    let nn = n as int;
                    assert(max_seq(b@) <= nn < (n + 1) as int);
                    assert(nn * (nn + 1) / 2 == sum_seq(b@) + s as int);
                }
            }
            n += 1;
        }
        proof {
            assert(n == 101);
            assert(found == (exists|nn: int| max_seq(b@) <= nn < 101 && #[trigger] (nn * (nn + 1) / 2) == sum_seq(b@) + s as int));
            
            
            
            
            
        }
        proof {
            assert(found == (exists|nn: int| max_seq(b@) <= nn <= 100 && #[trigger] (nn * (nn + 1) / 2) == sum_seq(b@) + s as int));
        }
        found
    }
}

}
