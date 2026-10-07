use vstd::prelude::*;

verus! {

pub fn generate_test_case(raw_piles: Vec<i32>, raw_queries: Vec<i32>) -> (result: (Vec<i32>, Vec<i32>))
    ensures 1 <= result.0.len() <= 100000, 1 <= result.1.len() <= 100000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1000,
        prefix_sum(result.0@, result.0.len() as int) <= 1000000,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= prefix_sum(result.0@, result.0.len() as int),
{
    let n = if raw_piles.len() == 0 { 1usize } else if raw_piles.len() > 100000 { 100000usize } else { raw_piles.len() };
    let m = if raw_queries.len() == 0 { 1usize } else if raw_queries.len() > 100000 { 100000usize } else { raw_queries.len() };
    let mut piles = Vec::new();
    let mut total = 0i32;
    let mut i = 0usize;
    while i < n
        invariant i <= n, 1 <= n <= 100000, piles.len() == i,
            i <= total <= 1000000 - (n - i),
            total == prefix_sum(piles@, piles.len() as int),
            forall|j: int| 0 <= j < i ==> 1 <= #[trigger] piles[j] <= 1000,
        decreases n - i,
    {
        let ceiling = 1000000 - total - ((n - i - 1) as i32);
        let ceiling = if ceiling > 1000 { 1000 } else { ceiling };
        let v = if i < raw_piles.len() { raw_piles[i] } else { 1 };
        let v = if v < 1 { 1 } else if v > ceiling { ceiling } else { v };
        proof { lemma_prefix_sum_push(piles@, v); }
        piles.push(v);
        total += v;
        i += 1;
    }
    let mut queries = Vec::new();
    let mut i = 0usize;
    while i < m
        invariant i <= m, 1 <= m <= 100000, queries.len() == i, 1 <= total <= 1000000,
            forall|j: int| 0 <= j < i ==> 1 <= #[trigger] queries[j] <= total,
        decreases m - i,
    {
        let v = if i < raw_queries.len() { raw_queries[i] } else { 1 };
        queries.push(if v < 1 { 1 } else if v > total { total } else { v });
        i += 1;
    }
    (piles, queries)
}


pub open spec fn prefix_sum_nat(piles: Seq<i32>, end: nat) -> int
    decreases end,
{
    if end == 0 {
        0
    } else {
        prefix_sum_nat(piles, (end - 1) as nat) + piles[end as int - 1] as int
    }
}

pub open spec fn prefix_sum(piles: Seq<i32>, end: int) -> int
    recommends
        0 <= end && end <= piles.len(),
{
    prefix_sum_nat(piles, end as nat)
}

// Proves prefix_sum is unchanged for indices below the push
proof fn lemma_prefix_sum_append(s: Seq<i32>, v: i32, end: nat)
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

// Proves prefix_sum after push extends by the pushed value
proof fn lemma_prefix_sum_push(s: Seq<i32>, v: i32)
    ensures
        prefix_sum(s.push(v), (s.len() + 1) as int)
            == prefix_sum(s, s.len() as int) + v as int,
{
    lemma_prefix_sum_append(s, v, s.len() as nat);
    assert(s.push(v)[s.len() as int] == v);
}

pub fn generate_candidate(
    pile_vals: Vec<i32>,
    query_seeds: Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= pile_vals.len() && pile_vals.len() <= 100_000,
        1 <= query_seeds.len() && query_seeds.len() <= 100_000,
        forall|i: int| 0 <= i < pile_vals.len() ==> 1 <= #[trigger] pile_vals[i] && pile_vals[i] <= 1000,
        forall|i: int| 0 <= i < query_seeds.len() ==> 1 <= #[trigger] query_seeds[i] && query_seeds[i] <= 1_000_000,
    ensures
        1 <= result.0.len() && result.0.len() <= 100_000,
        1 <= result.1.len() && result.1.len() <= 100_000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] && result.0[i] <= 1000,
        prefix_sum(result.0@, result.0.len() as int) <= 1_000_000,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] (result.1[i] as int) && (result.1[i] as int) <= prefix_sum(result.0@, result.0.len() as int),
{
    // Build piles by taking elements from pile_vals until sum would exceed 1_000_000
    let mut piles: Vec<i32> = Vec::new();

    // Always add the first element (in [1, 1000], always fits)
    let v0 = pile_vals[0];
    proof { lemma_prefix_sum_push(piles@, v0); }
    piles.push(v0);
    let mut sum: i32 = v0;

    let mut i: usize = 1;
    while i < pile_vals.len()
        invariant
            1 <= i <= pile_vals.len(),
            pile_vals.len() <= 100_000,
            1 <= piles.len() && piles.len() <= i,
            1 <= sum && sum <= 1_000_000,
            sum as int == prefix_sum(piles@, piles.len() as int),
            forall|j: int| 0 <= j < piles.len() ==> 1 <= #[trigger] piles[j] && piles[j] <= 1000,
            forall|j: int| 0 <= j < pile_vals.len() ==> 1 <= #[trigger] pile_vals[j] && pile_vals[j] <= 1000,
        decreases pile_vals.len() - i,
    {
        let v = pile_vals[i];
        if (sum as i64) + (v as i64) <= 1_000_000i64 {
            proof { lemma_prefix_sum_push(piles@, v); }
            piles.push(v);
            sum = sum + v;
        }
        i = i + 1;
    }

    let total_sum = sum;

    // Build queries based on mutation_kind
    let mut queries: Vec<i32> = Vec::new();

    if mutation_kind == 1 {
        // All queries = 1 (minimum boundary)
        let mut j: usize = 0;
        while j < query_seeds.len()
            invariant
                0 <= j <= query_seeds.len(),
                query_seeds.len() <= 100_000,
                queries.len() == j,
                total_sum >= 1,
                total_sum as int == prefix_sum(piles@, piles.len() as int),
                forall|k: int| 0 <= k < queries.len() ==> #[trigger] queries[k] == 1,
            decreases query_seeds.len() - j,
        {
            queries.push(1i32);
            j = j + 1;
        }
        assert forall|k: int| 0 <= k < queries.len()
            implies 1 <= #[trigger] (queries[k] as int)
                && (queries[k] as int) <= prefix_sum(piles@, piles.len() as int)
        by {
            assert(queries[k] == 1);
        }
    } else if mutation_kind == 2 {
        // All queries = total_sum (maximum boundary)
        let mut j: usize = 0;
        while j < query_seeds.len()
            invariant
                0 <= j <= query_seeds.len(),
                query_seeds.len() <= 100_000,
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
        // Normal: clamp each seed to [1, total_sum] using modular arithmetic
        let mut j: usize = 0;
        while j < query_seeds.len()
            invariant
                0 <= j <= query_seeds.len(),
                query_seeds.len() <= 100_000,
                queries.len() == j,
                total_sum >= 1,
                total_sum as int == prefix_sum(piles@, piles.len() as int),
                forall|k: int| 0 <= k < queries.len()
                    ==> 1 <= #[trigger] (queries[k] as int)
                        && (queries[k] as int) <= total_sum as int,
                forall|k: int| 0 <= k < query_seeds.len()
                    ==> 1 <= #[trigger] query_seeds[k] && query_seeds[k] <= 1_000_000,
            decreases query_seeds.len() - j,
        {
            let seed = query_seeds[j];
            let q = 1i32 + ((seed - 1) % total_sum);
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
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
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

fn build_input(piles: &[i32], queries: &[i32]) -> String {
    let n = piles.len();
    let m = queries.len();
    let mut s = format!("{}\n", n);
    let p_parts: Vec<String> = piles.iter().map(|x| x.to_string()).collect();
    s.push_str(&p_parts.join(" "));
    s.push('\n');
    s.push_str(&format!("{}\n", m));
    let q_parts: Vec<String> = queries.iter().map(|x| x.to_string()).collect();
    s.push_str(&q_parts.join(" "));
    s.push('\n');
    s
}

fn build_output(ans: &[i32]) -> String {
    let mut s = String::new();
    for &a in ans {
        s.push_str(&format!("{}\n", a));
    }
    s
}

fn main() {
    let target_count: usize = 100;
    let mut rng = Rng::new(474);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |piles: Vec<i32>, queries: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        if piles.is_empty() || queries.is_empty() { return; }
        let total: i64 = piles.iter().map(|&x| x as i64).sum();
        if queries.iter().any(|&q| q < 1 || q as i64 > total) { return; }
        let key = format!("{:?}_{:?}", piles, queries);
        if !seen.insert(key) { return; }
        let (piles, queries) = generate_test_case(piles, queries);
        let result = Solution::find_worm_piles(piles.clone(), queries.clone());
        let inp = build_input(&piles, &queries);
        let outp = build_output(&result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    emit(vec![2, 7, 3, 4, 9], vec![1, 25, 11], &mut seen, &mut out, &mut count);

    emit(vec![1], vec![1], &mut seen, &mut out, &mut count);
    emit(vec![1000], vec![1, 500, 1000], &mut seen, &mut out, &mut count);
    emit(vec![1, 1, 1, 1, 1], vec![1, 2, 3, 4, 5], &mut seen, &mut out, &mut count);
    emit(vec![5, 5, 5, 5, 5], vec![1, 5, 6, 25], &mut seen, &mut out, &mut count);
    emit(vec![1000, 1, 1000], vec![1000, 1001, 2001], &mut seen, &mut out, &mut count);

    while count < target_count {
        let n = match count % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(2, 30),
            2 => rng.gen_range_usize(30, 200),
            3 => rng.gen_range_usize(200, 1000),
            _ => rng.gen_range_usize(500, 5000),
        };
        let piles: Vec<i32> = (0..n).map(|_| rng.gen_range_i64(1, 1000) as i32).collect();
        let total: i64 = piles.iter().map(|&x| x as i64).sum();
        let m = rng.gen_range_usize(1, 100);
        let queries: Vec<i32> = (0..m).map(|_| rng.gen_range_i64(1, total) as i32).collect();
        emit(piles, queries, &mut seen, &mut out, &mut count);
    }
}
