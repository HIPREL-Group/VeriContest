use vstd::prelude::*;

verus! {

pub open spec fn prefix_sum_nat(piles: Seq<i64>, end: nat) -> int
    decreases end,
{
    if end == 0 {
        0
    } else {
        prefix_sum_nat(piles, (end - 1) as nat) + piles[end as int - 1] as int
    }
}

pub open spec fn prefix_sum(piles: Seq<i64>, end: int) -> int
    recommends
        0 <= end && end <= piles.len(),
{
    prefix_sum_nat(piles, end as nat)
}

proof fn lemma_prefix_sum_append(s: Seq<i64>, v: i64, end: nat)
    requires
        end <= s.len(),
    ensures
        prefix_sum_nat(s.push(v), end) == prefix_sum_nat(s, end),
    decreases end,
{
    if end > 0 {
        lemma_prefix_sum_append(s, v, (end - 1) as nat);
        assert(s.push(v)[end as int - 1] == s[end as int - 1]);
    }
}

proof fn lemma_prefix_sum_push(s: Seq<i64>, v: i64)
    ensures
        prefix_sum(s.push(v), (s.len() + 1) as int)
            == prefix_sum(s, s.len() as int) + v as int,
{
    lemma_prefix_sum_append(s, v, s.len() as nat);
    assert(s.push(v)[s.len() as int] == v);
}

pub fn generate_test_case(
    pile_vals: Vec<i64>,
    query_seeds: Vec<i64>,
    mutation_kind: u8,
) -> (result: (Vec<i64>, Vec<i64>))
    requires
        1 <= pile_vals.len() && pile_vals.len() <= 200_000,
        1 <= query_seeds.len() && query_seeds.len() <= 200_000,
        forall|i: int| 0 <= i < pile_vals.len()
            ==> 1 <= #[trigger] pile_vals[i] as int && (pile_vals[i] as int) <= 10_000_000_000,
        forall|i: int| 0 <= i < query_seeds.len()
            ==> 1 <= #[trigger] query_seeds[i] as int && (query_seeds[i] as int) <= 10_000_000_000,
    ensures
        1 <= result.0.len() && result.0.len() <= 200_000,
        1 <= result.1.len() && result.1.len() <= 200_000,
        forall|i: int| 0 <= i < result.0.len()
            ==> 1 <= #[trigger] result.0[i] as int && (result.0[i] as int) <= 10_000_000_000,
        prefix_sum(result.0@, result.0.len() as int) <= 9_223_372_036_854_775_807,
        forall|i: int| 0 <= i < result.1.len()
            ==> 1 <= #[trigger] (result.1[i] as int)
                && (result.1[i] as int) <= prefix_sum(result.0@, result.0.len() as int),
{
    // Build piles from pile_vals, skipping elements that would overflow
    let mut piles: Vec<i64> = Vec::new();

    let v0 = pile_vals[0];
    proof { lemma_prefix_sum_push(piles@, v0); }
    piles.push(v0);
    let mut sum: i64 = v0;

    let mut i: usize = 1;
    while i < pile_vals.len()
        invariant
            1 <= i <= pile_vals.len(),
            pile_vals.len() <= 200_000,
            1 <= piles.len() && piles.len() <= i,
            1 <= sum,
            sum as int <= 9_223_372_036_854_775_807,
            sum as int == prefix_sum(piles@, piles.len() as int),
            forall|j: int| 0 <= j < piles.len()
                ==> 1 <= #[trigger] piles[j] as int && (piles[j] as int) <= 10_000_000_000,
            forall|j: int| 0 <= j < pile_vals.len()
                ==> 1 <= #[trigger] pile_vals[j] as int && (pile_vals[j] as int) <= 10_000_000_000,
        decreases pile_vals.len() - i,
    {
        let v = pile_vals[i];
        if sum <= 9_223_372_036_854_775_807i64 - v {
            proof { lemma_prefix_sum_push(piles@, v); }
            piles.push(v);
            sum = sum + v;
        }
        i = i + 1;
    }

    let total_sum = sum;

    // Build queries based on mutation_kind
    let mut queries: Vec<i64> = Vec::new();

    if mutation_kind == 1 {
        // All queries = 1 (minimum boundary)
        let mut j: usize = 0;
        while j < query_seeds.len()
            invariant
                0 <= j <= query_seeds.len(),
                query_seeds.len() <= 200_000,
                queries.len() == j,
                total_sum >= 1,
                total_sum as int == prefix_sum(piles@, piles.len() as int),
                forall|k: int| 0 <= k < queries.len() ==> #[trigger] queries[k] == 1i64,
            decreases query_seeds.len() - j,
        {
            queries.push(1i64);
            j = j + 1;
        }
        assert forall|k: int| 0 <= k < queries.len()
            implies 1 <= #[trigger] (queries[k] as int)
                && (queries[k] as int) <= prefix_sum(piles@, piles.len() as int)
        by {
            assert(queries[k] == 1i64);
        }
    } else if mutation_kind == 2 {
        // All queries = total_sum (maximum boundary)
        let mut j: usize = 0;
        while j < query_seeds.len()
            invariant
                0 <= j <= query_seeds.len(),
                query_seeds.len() <= 200_000,
                queries.len() == j,
                total_sum >= 1,
                total_sum as int == prefix_sum(piles@, piles.len() as int),
                forall|k: int| 0 <= k < queries.len() ==> #[trigger] queries[k] == total_sum,
            decreases query_seeds.len() - j,
        {
            queries.push(total_sum);
            j = j + 1;
        }
        assert forall|k: int| 0 <= k < queries.len()
            implies 1 <= #[trigger] (queries[k] as int)
                && (queries[k] as int) <= prefix_sum(piles@, piles.len() as int)
        by {
            assert(queries[k] == total_sum);
        }
    } else {
        // Normal: clamp each seed to [1, total_sum]
        let mut j: usize = 0;
        while j < query_seeds.len()
            invariant
                0 <= j <= query_seeds.len(),
                query_seeds.len() <= 200_000,
                queries.len() == j,
                total_sum >= 1,
                total_sum as int == prefix_sum(piles@, piles.len() as int),
                forall|k: int| 0 <= k < queries.len()
                    ==> 1 <= #[trigger] (queries[k] as int)
                        && (queries[k] as int) <= total_sum as int,
                forall|k: int| 0 <= k < query_seeds.len()
                    ==> 1 <= #[trigger] query_seeds[k] as int
                        && (query_seeds[k] as int) <= 10_000_000_000,
            decreases query_seeds.len() - j,
        {
            let seed = query_seeds[j];
            let q = 1i64 + ((seed - 1) % total_sum);
            queries.push(q);
            j = j + 1;
        }
        assert forall|k: int| 0 <= k < queries.len()
            implies 1 <= #[trigger] (queries[k] as int)
                && (queries[k] as int) <= prefix_sum(piles@, piles.len() as int)
        by {}
    }

    (piles, queries)
}

}

use std::io::Write;
use std::collections::HashSet;

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let r = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % r) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

fn fmt_json_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

struct Solution;
include!("../code.rs");

fn build_input(piles: &[i64], queries: &[i64]) -> String {
    let mut s = format!("{} {}\n", piles.len(), queries.len());
    let parts: Vec<String> = piles.iter().map(|v| v.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    let qparts: Vec<String> = queries.iter().map(|v| v.to_string()).collect();
    s.push_str(&qparts.join(" "));
    s.push('\n');
    s
}

fn build_output(ans: &[(i64, i64)]) -> String {
    let mut s = String::new();
    for (f, k) in ans { s.push_str(&format!("{} {}\n", f, k)); }
    s
}

fn make_strict_inc_queries(rng: &mut Rng, m: usize, total: i64) -> Vec<i64> {
    let mut s: Vec<i64> = Vec::with_capacity(m);
    let mut used: HashSet<i64> = HashSet::new();
    let mut tries = 0;
    while s.len() < m && tries < m * 50 {
        tries += 1;
        let v = rng.gen_range_i64(1, total);
        if used.insert(v) { s.push(v); }
    }
    if s.len() < m { return Vec::new(); }
    s.sort_unstable();
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(978);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |piles: Vec<i64>, queries: Vec<i64>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if piles.is_empty() || piles.len() > 200_000 || queries.is_empty() || queries.len() > 200_000 { return; }
        for &v in &piles { if v < 1 || v > 10_000_000_000 { return; } }
        let total: i64 = piles.iter().sum();
        for &q in &queries { if q < 1 || q > total { return; } }
        for w in queries.windows(2) { if w[0] >= w[1] { return; } }
        let key = format!("{:?}|{:?}", piles, queries);
        if !seen.insert(key) { return; }
        let inp = build_input(&piles, &queries);
        let ans = Solution::deliver_letters(piles.clone(), queries.clone());
        let outs = build_output(&ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Examples
    emit(vec![10, 15, 12], vec![1, 9, 12, 23, 26, 37], &mut seen, &mut out, &mut count);
    emit(vec![5, 10_000_000_000], vec![5, 6, 9_999_999_999], &mut seen, &mut out, &mut count);

    // Edges
    emit(vec![1], vec![1], &mut seen, &mut out, &mut count);
    emit(vec![10_000_000_000], vec![10_000_000_000], &mut seen, &mut out, &mut count);
    emit(vec![1, 1, 1], vec![1, 2, 3], &mut seen, &mut out, &mut count);

    while count < target {
        let n = rng.gen_range_usize(1, 100);
        let m = rng.gen_range_usize(1, 100);
        let piles: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, 1000)).collect();
        let total: i64 = piles.iter().sum();
        if total < m as i64 { continue; }
        let queries = make_strict_inc_queries(&mut rng, m, total);
        if queries.is_empty() { continue; }
        emit(piles, queries, &mut seen, &mut out, &mut count);
    }
}

