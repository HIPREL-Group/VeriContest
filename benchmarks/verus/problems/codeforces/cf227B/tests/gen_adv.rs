use vstd::prelude::*;

verus! {

pub open spec fn value_occurs(permutation: Seq<i32>, value: int) -> bool {
    exists|pos: int| 0 <= pos < permutation.len() && permutation[pos] == value
}

pub open spec fn all_values_occur(permutation: Seq<i32>) -> bool {
    forall|value: int| 1 <= value <= permutation.len() ==> #[trigger] value_occurs(permutation, value)
}

pub open spec fn is_valid_permutation(permutation: Seq<i32>) -> bool {
    1 <= permutation.len() <= 100_000
        && forall|i: int| 0 <= i < permutation.len() ==> 1 <= #[trigger] permutation[i] <= permutation.len()
        && forall|i: int, j: int| 0 <= i < j < permutation.len() ==> permutation[i] != permutation[j]
        && all_values_occur(permutation)
}

pub open spec fn are_valid_queries(queries: Seq<i32>, n: int) -> bool {
    1 <= queries.len() <= 100_000
        && forall|i: int| 0 <= i < queries.len() ==> 1 <= #[trigger] queries[i] <= n
}

// Generate the identity permutation [1, 2, ..., n]
pub fn gen_identity_perm(n: usize) -> (perm: Vec<i32>)
    requires
        1 <= n <= 100_000,
    ensures
        perm.len() == n,
        1 <= perm.len() <= 100_000,
        forall|i: int| 0 <= i < perm.len() ==> #[trigger] perm[i] == (i + 1) as i32,
        forall|i: int| 0 <= i < perm.len() ==> 1 <= #[trigger] perm[i] <= perm.len(),
        forall|i: int, j: int| 0 <= i < j < perm.len() ==> perm[i] != perm[j],
        all_values_occur(perm@),
        is_valid_permutation(perm@),
{
    let mut perm: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            1 <= n <= 100_000,
            0 <= i <= n,
            perm.len() == i,
            forall|j: int| 0 <= j < i as int ==> #[trigger] perm[j] == (j + 1) as i32,
        decreases n - i,
    {
        perm.push((i + 1) as i32);
        i = i + 1;
    }
    // prove validity
    assert(perm.len() == n);
    assert(forall|j: int| 0 <= j < perm.len() ==> 1 <= #[trigger] perm[j] <= perm.len()) by {
        assert(forall|j: int| 0 <= j < perm.len() ==> perm[j] == (j + 1) as i32);
    };
    assert(forall|j: int, k: int| 0 <= j < k < perm.len() ==> perm[j] != perm[k]) by {
        assert(forall|j: int| 0 <= j < perm.len() ==> perm[j] == (j + 1) as i32);
    };
    assert(all_values_occur(perm@)) by {
        assert forall|value: int| 1 <= value <= perm.len() implies #[trigger] value_occurs(perm@, value) by {
            let pos: int = value - 1;
            assert(0 <= pos < perm@.len());
            assert(perm@[pos] == value);
        }
    };
    perm
}

// Generate the reversed permutation [n, n-1, ..., 1]
pub fn gen_reverse_perm(n: usize) -> (perm: Vec<i32>)
    requires
        1 <= n <= 100_000,
    ensures
        perm.len() == n,
        1 <= perm.len() <= 100_000,
        forall|i: int| 0 <= i < perm.len() ==> #[trigger] perm[i] == (n - i) as i32,
        forall|i: int| 0 <= i < perm.len() ==> 1 <= #[trigger] perm[i] <= perm.len(),
        forall|i: int, j: int| 0 <= i < j < perm.len() ==> perm[i] != perm[j],
        all_values_occur(perm@),
        is_valid_permutation(perm@),
{
    let mut perm: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            1 <= n <= 100_000,
            0 <= i <= n,
            perm.len() == i,
            forall|j: int| 0 <= j < i as int ==> #[trigger] perm[j] == (n - j) as i32,
        decreases n - i,
    {
        perm.push((n - i) as i32);
        i = i + 1;
    }
    assert(perm.len() == n);
    assert(forall|j: int| 0 <= j < perm.len() ==> 1 <= #[trigger] perm[j] <= perm.len()) by {
        assert(forall|j: int| 0 <= j < perm.len() ==> perm[j] == (n - j) as i32);
    };
    assert(forall|j: int, k: int| 0 <= j < k < perm.len() ==> perm[j] != perm[k]) by {
        assert(forall|j: int| 0 <= j < perm.len() ==> perm[j] == (n - j) as i32);
    };
    assert(all_values_occur(perm@)) by {
        assert forall|value: int| 1 <= value <= perm.len() implies #[trigger] value_occurs(perm@, value) by {
            let pos: int = (n as int) - value;
            assert(0 <= pos < perm@.len());
            assert(perm@[pos] == (n - pos) as i32);
            assert((n - pos) as i32 == value);
        }
    };
    perm
}

pub fn generate_test_case(
    seed_n: usize,
    seed_m: usize,
    seed_q_fillers: &Vec<i32>,
    perm_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= seed_n <= 100_000,
        1 <= seed_m <= 100_000,
        seed_q_fillers.len() == seed_m,
        forall|i: int| 0 <= i < seed_q_fillers.len() ==> 1 <= #[trigger] seed_q_fillers[i] <= seed_n as i32,
    ensures
        is_valid_permutation(result.0@),
        all_values_occur(result.0@),
        result.0.len() == seed_n,
        are_valid_queries(result.1@, result.0.len() as int),
{
    let perm = if perm_kind == 0 {
        gen_identity_perm(seed_n)
    } else {
        gen_reverse_perm(seed_n)
    };
    // Copy queries
    let mut queries: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < seed_m
        invariant
            seed_q_fillers.len() == seed_m,
            1 <= seed_m <= 100_000,
            0 <= i <= seed_m,
            queries.len() == i,
            perm.len() == seed_n,
            1 <= seed_n <= 100_000,
            forall|j: int| 0 <= j < seed_q_fillers.len() ==> 1 <= #[trigger] seed_q_fillers[j] <= seed_n as i32,
            forall|j: int| 0 <= j < i as int ==> #[trigger] queries[j] == seed_q_fillers[j],
        decreases seed_m - i,
    {
        queries.push(seed_q_fillers[i]);
        i = i + 1;
    }
    assert(queries.len() == seed_m);
    assert(forall|j: int| 0 <= j < queries.len() ==> 1 <= #[trigger] queries[j] <= seed_n as i32) by {
        assert(forall|j: int| 0 <= j < queries.len() ==> queries[j] == seed_q_fillers[j]);
        assert(forall|j: int| 0 <= j < seed_q_fillers.len() ==> 1 <= #[trigger] seed_q_fillers[j] <= seed_n as i32);
    };
    (perm, queries)
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

fn build_input(perm: &[i32], queries: &[i32]) -> String {
    let mut s = format!("{}\n", perm.len());
    let parts: Vec<String> = perm.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s.push_str(&format!("{}\n", queries.len()));
    let qparts: Vec<String> = queries.iter().map(|x| x.to_string()).collect();
    s.push_str(&qparts.join(" "));
    s.push('\n');
    s
}

fn build_output(vasya: i64, petya: i64) -> String {
    format!("{} {}\n", vasya, petya)
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(0x227B);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    while count < target {
        let n = match count % 6 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(2, 20),
            2 => rng.gen_range_usize(20, 100),
            3 => rng.gen_range_usize(100, 1000),
            4 => rng.gen_range_usize(1000, 10000),
            _ => rng.gen_range_usize(10000, 100000),
        };
        let m = match count % 4 {
            0 => rng.gen_range_usize(1, 10),
            1 => rng.gen_range_usize(1, 100),
            2 => rng.gen_range_usize(1, 10000),
            _ => rng.gen_range_usize(1, 100000),
        };
        // Validate seed
        if n < 1 || n > 100_000 { continue; }
        if m < 1 || m > 100_000 { continue; }
        let seed_q: Vec<i32> = (0..m).map(|_| rng.gen_range_i64(1, n as i64) as i32).collect();
        let mut ok = true;
        for &v in &seed_q {
            if v < 1 || v > n as i32 { ok = false; break; }
        }
        if !ok { continue; }
        let perm_kind = ((count + (rng.next_u64() >> 32) as usize) % 2) as u8;
        let (p, q) = generate_test_case(n, m, &seed_q, perm_kind);
        let inp = build_input(&p, &q);
        if !seen.insert(inp.clone()) { continue; }
        let (vv, pe) = Solution::effective_approach(p, q);
        let outp = build_output(vv, pe);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
