use vstd::prelude::*;

verus! {

// Spec fn helpers copied from spec.rs

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

/// Constructs a valid (permutation, queries) pair from construction parameters.
///
/// Builds an identity permutation [1, 2, ..., n] and optionally swaps two
/// positions (when mutation_kind >= 1 and swap_a != swap_b) for diversity.
/// Query values are passed through as a construction parameter.
pub fn generate_test_case(
    n: u32,
    swap_a: u32,
    swap_b: u32,
    query_vals: Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= n <= 1000,
        swap_a < n,
        swap_b < n,
        1 <= query_vals.len() <= 1000,
        forall|i: int| 0 <= i < query_vals.len() ==> 1 <= #[trigger] query_vals[i] <= n as i32,
    ensures
        is_valid_permutation(result.0@),
        all_values_occur(result.0@),
        are_valid_queries(result.1@, result.0.len() as int),
{
    // Build identity permutation [1, 2, ..., n]
    let mut perm: Vec<i32> = Vec::new();
    let mut idx: u32 = 0;
    while idx < n
        invariant
            0 <= idx <= n,
            1 <= n <= 1000,
            perm.len() == idx as int,
            forall|j: int| 0 <= j < idx as int ==> perm@[j] == (j + 1) as i32,
        decreases n - idx,
    {
        perm.push((idx + 1) as i32);
        idx += 1;
    }

    if mutation_kind >= 1 && swap_a != swap_b {
        let va = perm[swap_a as usize];
        let vb = perm[swap_b as usize];

        perm.set(swap_a as usize, vb);
        perm.set(swap_b as usize, va);

        proof {
            let s = perm@;
            let len = s.len();

            // All elements in range [1, n]
            assert forall|k: int| 0 <= k < len
                implies 1 <= #[trigger] s[k] <= len
            by {
                if k == swap_a as int {
                } else if k == swap_b as int {
                } else {
                }
            };

            // All elements distinct
            assert forall|ii: int, jj: int|
                0 <= ii < jj < len
                implies s[ii] != s[jj]
            by {
                if ii == swap_a as int {
                    if jj == swap_b as int {
                    } else {
                    }
                } else if ii == swap_b as int {
                    if jj == swap_a as int {
                    } else {
                    }
                } else {
                    if jj == swap_a as int {
                    } else if jj == swap_b as int {
                    } else {
                    }
                }
            };

            // All values 1..=n occur (provide existential witnesses)
            assert forall|v: int| 1 <= v <= len
                implies #[trigger] value_occurs(s, v)
            by {
                if v == swap_a as int + 1 {
                    assert(s[swap_b as int] == v);
                } else if v == swap_b as int + 1 {
                    assert(s[swap_a as int] == v);
                } else {
                    assert(s[v - 1] == v);
                }
            };
        }
    } else {
        // No swap — identity permutation [1, 2, ..., n]
        proof {
            let s = perm@;
            let len = s.len();

            assert forall|k: int| 0 <= k < len
                implies 1 <= #[trigger] s[k] <= len
            by {};

            assert forall|ii: int, jj: int|
                0 <= ii < jj < len
                implies s[ii] != s[jj]
            by {};

            assert forall|v: int| 1 <= v <= len
                implies #[trigger] value_occurs(s, v)
            by {
                assert(s[v - 1] == v);
            };
        }
    }

    (perm, query_vals)
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

fn random_perm(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = (1..=(n as i32)).collect();
    // Fisher-Yates
    for i in (1..n).rev() {
        let j = rng.gen_range_usize(0, i);
        v.swap(i, j);
    }
    v
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(227);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let examples: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![1, 2], vec![1]),
        (vec![2, 1], vec![1]),
        (vec![3, 1, 2, 5, 4], vec![1, 2, 3, 4, 5]),
        (vec![1], vec![1, 1, 1]),
    ];
    for (p, q) in &examples {
        if count >= target { break; }
        let inp = build_input(p, q);
        if !seen.insert(inp.clone()) { continue; }
        let (v, pe) = Solution::effective_approach(p.clone(), q.clone());
        let outp = build_output(v, pe);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    while count < target {
        let n = match count % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(2, 20),
            2 => rng.gen_range_usize(20, 100),
            3 => rng.gen_range_usize(100, 1000),
            _ => rng.gen_range_usize(1000, 10000),
        };
        let m = match count % 3 {
            0 => rng.gen_range_usize(1, n.max(10)),
            1 => rng.gen_range_usize(1, 10),
            _ => rng.gen_range_usize(1, 1000.min(100_000)),
        };
        let p = random_perm(&mut rng, n);
        let q: Vec<i32> = (0..m).map(|_| rng.gen_range_i64(1, n as i64) as i32).collect();
        let inp = build_input(&p, &q);
        if !seen.insert(inp.clone()) { continue; }
        let (v, pe) = Solution::effective_approach(p, q);
        let outp = build_output(v, pe);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

