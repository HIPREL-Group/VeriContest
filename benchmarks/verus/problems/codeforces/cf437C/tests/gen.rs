use vstd::prelude::*;

verus! {

pub open spec fn same_undirected_edge(a: (usize, usize), b: (usize, usize)) -> bool {
    (a.0 == b.0 && a.1 == b.1) || (a.0 == b.1 && a.1 == b.0)
}

pub open spec fn valid_edge(weights: Seq<i64>, edge: (usize, usize)) -> bool {
    edge.0 < weights.len() && edge.1 < weights.len() && edge.0 != edge.1
}

pub fn generate_test_case(
    n: usize,
    num_edges: usize,
    weight_val: i64,
    mutation_kind: u8,
) -> (result: (Vec<i64>, Vec<(usize, usize)>))
    requires
        1 <= n <= 1000,
        num_edges < n,
        num_edges <= 2000,
        0 <= weight_val <= 100_000,
    ensures
        1 <= result.0.len() <= 1000,
        0 <= result.1.len() <= 2000,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0@[i] && result.0@[i] <= 100_000,
        forall|k: int| 0 <= k < result.1.len() ==> #[trigger] valid_edge(result.0@, result.1@[k]),
        forall|i: int, j: int|
            0 <= i < j < result.1.len() ==> !same_undirected_edge(result.1@[i], result.1@[j]),
{
    // Select weight based on mutation
    let w: i64 = if mutation_kind == 1 {
        0i64
    } else if mutation_kind == 2 {
        100_000i64
    } else {
        weight_val
    };

    // Build weights: all set to w
    let mut weights: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            1 <= n <= 1000,
            0 <= w <= 100_000,
            weights.len() == i,
            forall|j: int| 0 <= j < i as int ==> weights@[j] == w,
        decreases n - i,
    {
        weights.push(w);
        i += 1;
    }

    // Build star edges from node 0: (0, 1), (0, 2), ..., (0, num_edges)
    let mut edges: Vec<(usize, usize)> = Vec::new();
    let mut e: usize = 0;
    while e < num_edges
        invariant
            0 <= e <= num_edges,
            num_edges < n,
            num_edges <= 2000,
            weights.len() == n,
            edges.len() == e,
            forall|k: int| 0 <= k < e as int ==>
                edges@[k] == (0usize, (k + 1) as usize),
        decreases num_edges - e,
    {
        edges.push((0usize, e + 1));
        e += 1;
    }

    proof {
        // Weight bounds
        assert forall|i: int| 0 <= i < weights@.len() implies
            (0 <= #[trigger] weights@[i] && weights@[i] <= 100_000) by
        {
            assert(weights@[i] == w);
        };

        // Valid edges
        assert forall|k: int| 0 <= k < edges@.len() implies
            #[trigger] valid_edge(weights@, edges@[k]) by
        {
            let edge = edges@[k];
            assert(edge == (0usize, (k + 1) as usize));
            assert(edge.0 == 0usize);
            assert(edge.1 == (k + 1) as usize);
            assert(edge.0 < weights@.len());
            assert((edge.1 as int) < weights@.len() as int);
            assert(edge.0 != edge.1);
        };

        // Unique edges
        assert forall|i: int, j: int| 0 <= i < j < edges@.len() implies
            !same_undirected_edge(edges@[i], edges@[j]) by
        {
            let ei = edges@[i];
            let ej = edges@[j];
            assert(ei == (0usize, (i + 1) as usize));
            assert(ej == (0usize, (j + 1) as usize));
            // First disjunct of same_undirected_edge: ei.0==ej.0 && ei.1==ej.1
            // ei.1 = i+1, ej.1 = j+1, i < j so i+1 != j+1
            assert(ei.1 != ej.1);
            // Second disjunct: ei.0==ej.1 && ei.1==ej.0
            // ei.0 = 0, ej.1 = j+1 >= 1, so 0 != j+1
            assert(ei.0 != ej.1);
        };
    }

    (weights, edges)
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

fn build_input(weights: &[i64], edges: &[(usize, usize)]) -> String {
    let n = weights.len();
    let m = edges.len();
    let mut s = format!("{} {}\n", n, m);
    let parts: Vec<String> = weights.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    for &(u, v) in edges {
        s.push_str(&format!("{} {}\n", u + 1, v + 1));
    }
    s
}

fn random_edges(rng: &mut Rng, n: usize, m: usize) -> Vec<(usize, usize)> {
    let mut edges = Vec::new();
    let mut seen = HashSet::new();
    let mut tries = 0usize;
    while edges.len() < m && tries < m * 100 + 1000 {
        tries += 1;
        if n < 2 { break; }
        let a = rng.gen_range_usize(0, n - 1);
        let b = rng.gen_range_usize(0, n - 1);
        if a == b { continue; }
        let key = (a.min(b), a.max(b));
        if seen.insert(key) {
            edges.push((a, b));
        }
    }
    edges
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |weights: Vec<i64>, edges: Vec<(usize, usize)>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let n = weights.len();
        let m = edges.len();
        if !(1 <= n && n <= 1000 && m <= 2000) { return; }
        for &w in &weights { if !(0 <= w && w <= 100_000) { return; } }
        for &(u, v) in &edges { if !(u < n && v < n && u != v) { return; } }
        let key = format!("{:?}|{:?}", weights, edges);
        if !seen.insert(key) { return; }
        let inp = build_input(&weights, &edges);
        let ans = Solution::min_total_energy(weights.clone(), edges.clone());
        let outs = format!("{}\n", ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    emit(vec![10, 20, 30, 40], vec![(0, 3), (0, 1), (1, 2)], &mut seen, &mut out, &mut count);
    emit(vec![100, 100, 100, 100], vec![(0, 1), (1, 2), (1, 3), (2, 3)], &mut seen, &mut out, &mut count);
    emit(vec![0], vec![], &mut seen, &mut out, &mut count);
    emit(vec![100_000], vec![], &mut seen, &mut out, &mut count);
    emit(vec![5, 7], vec![], &mut seen, &mut out, &mut count);
    emit(vec![5, 7], vec![(0, 1)], &mut seen, &mut out, &mut count);

    let mut tries = 0usize;
    while count < target {
        tries += 1;
        if tries > 100000 { break; }
        let n = match tries % 5 {
            0 => 1,
            1 => rng.gen_range_usize(1, 5),
            2 => rng.gen_range_usize(5, 30),
            3 => rng.gen_range_usize(30, 200),
            _ => rng.gen_range_usize(200, 1000),
        };
        let max_m = std::cmp::min(2000usize, if n < 2 { 0 } else { n * (n-1) / 2 });
        let m = if max_m == 0 { 0 } else { rng.gen_range_usize(0, max_m) };
        let weights: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(0, 100_000)).collect();
        let edges = random_edges(&mut rng, n, m);
        emit(weights, edges, &mut seen, &mut out, &mut count);
    }
}

