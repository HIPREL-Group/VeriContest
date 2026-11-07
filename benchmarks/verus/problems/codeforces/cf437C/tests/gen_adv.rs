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
    weights_in: &Vec<i64>,
    edges_in: &Vec<(usize, usize)>,
) -> (res: (Vec<i64>, Vec<(usize, usize)>))
    requires
        1 <= n <= 1000,
        weights_in.len() == n,
        forall|i: int| 0 <= i < weights_in.len() ==> 0 <= #[trigger] weights_in[i] <= 100_000,
        0 <= edges_in.len() <= 2000,
        forall|k: int| 0 <= k < edges_in.len() ==> #[trigger] valid_edge(weights_in@, edges_in@[k]),
        forall|i: int, j: int|
            0 <= i < j < edges_in.len() ==> !same_undirected_edge(edges_in@[i], edges_in@[j]),
    ensures
        1 <= res.0.len() <= 1000,
        0 <= res.1.len() <= 2000,
        forall|i: int| 0 <= i < res.0.len() ==> 0 <= #[trigger] res.0@[i] && res.0@[i] <= 100_000,
        forall|k: int| 0 <= k < res.1.len() ==> #[trigger] valid_edge(res.0@, res.1@[k]),
        forall|i: int, j: int|
            0 <= i < j < res.1.len() ==> !same_undirected_edge(res.1@[i], res.1@[j]),
{
    let mut weights: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < weights_in.len()
        invariant
            i <= weights_in.len(),
            weights.len() == i,
            forall|k: int| 0 <= k < i as int ==> weights@[k] == weights_in@[k],
            forall|k: int| 0 <= k < weights_in.len() ==> 0 <= #[trigger] weights_in[k] <= 100_000,
        decreases weights_in.len() - i,
    {
        weights.push(weights_in[i]);
        i = i + 1;
    }

    assert(weights@ =~= weights_in@);

    let mut edges: Vec<(usize, usize)> = Vec::new();
    let mut j: usize = 0;
    while j < edges_in.len()
        invariant
            j <= edges_in.len(),
            edges.len() == j,
            forall|k: int| 0 <= k < j as int ==> edges@[k] == edges_in@[k],
        decreases edges_in.len() - j,
    {
        edges.push(edges_in[j]);
        j = j + 1;
    }

    assert(edges@ =~= edges_in@);

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

fn build_complete_path(n: usize) -> Vec<(usize, usize)> {
    (0..n.saturating_sub(1)).map(|i| (i, i+1)).collect()
}

fn build_star(n: usize) -> Vec<(usize, usize)> {
    (1..n).map(|i| (0, i)).collect()
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
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

    let mut tries = 0usize;
    while count < target {
        tries += 1;
        if tries > 100000 { break; }
        let mode = tries % 8;
        let n = match mode {
            0 => 1,
            1 => 1000,
            2 => 2,
            3 => rng.gen_range_usize(2, 10),
            4 => rng.gen_range_usize(50, 200),
            5 => 100,
            6 => 500,
            _ => rng.gen_range_usize(1, 1000),
        };
        let weights: Vec<i64> = match mode % 3 {
            0 => vec![100_000; n],
            1 => vec![0; n],
            _ => (0..n).map(|_| rng.gen_range_i64(0, 100_000)).collect(),
        };
        let edges = match mode % 4 {
            0 => {
                let max_m = std::cmp::min(2000, if n < 2 { 0 } else { n * (n-1) / 2 });
                let m = if max_m == 0 { 0 } else { rng.gen_range_usize(0, max_m) };
                random_edges(&mut rng, n, m)
            }
            1 => build_complete_path(n),
            2 => build_star(n.min(2001)),
            _ => Vec::new(),
        };
        emit(weights, edges, &mut seen, &mut out, &mut count);
    }
}

