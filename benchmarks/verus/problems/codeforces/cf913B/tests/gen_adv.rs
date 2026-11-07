use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    p: Vec<usize>,
) -> (result: (usize, Vec<usize>))
    requires
        n >= 3,
        n <= 1000,
        p.len() == n - 1,
        forall|i: int| 0 <= i && i < p.len() ==> p@[i] <= i as usize,
    ensures
        result.0 >= 3,
        result.0 <= 1000,
        result.1.len() == result.0 - 1,
        forall|i: int| 0 <= i && i < result.1.len() ==> result.1@[i] <= i as usize,
{
    (n, p)
}

pub fn build_parents(
    n: usize,
    choices: &Vec<usize>,
) -> (p: Vec<usize>)
    requires
        n >= 3,
        n <= 1000,
        choices.len() == n - 1,
        forall|i: int| 0 <= i && i < choices.len() ==> choices@[i] <= i as usize,
    ensures
        p.len() == n - 1,
        forall|i: int| 0 <= i && i < p.len() ==> p@[i] <= i as usize,
{
    let mut p: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    let len = choices.len();
    while i < len
        invariant
            len == choices.len(),
            len == n - 1,
            i <= len,
            p.len() == i,
            forall|k: int| 0 <= k && k < i as int ==> p@[k] <= k as usize,
            forall|k: int| 0 <= k && k < choices.len() ==> choices@[k] <= k as usize,
        decreases len - i,
    {
        p.push(choices[i]);
        i = i + 1;
    }
    p
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

fn build_input(n: usize, p_one_indexed: &[usize]) -> String {
    let mut s = format!("{}\n", n);
    for &pi in p_one_indexed { s.push_str(&format!("{}\n", pi)); }
    s
}

fn build_output(yes: bool) -> String { if yes { "Yes\n".into() } else { "No\n".into() } }

fn make_tree(rng: &mut Rng, n: usize) -> Vec<usize> {
    if n < 3 { return Vec::new(); }
    let mut p = Vec::with_capacity(n - 1);
    p.push(1);
    p.push(1);
    for i in 3..n {
        let par = rng.gen_range_usize(1, i);
        p.push(par);
    }
    p
}

// "Spruce" tree: every non-leaf has 3 leaf children
fn make_spruce(n_internal: usize) -> (usize, Vec<usize>) {
    // Each internal node gets 3 leaves attached. We'll build a chain of internal nodes plus leaves.
    // Internal vertex k has parent = some prior internal. The first one is the root.
    // total nodes = n_internal + 3 * n_internal = 4 * n_internal
    if n_internal == 0 { return (3, vec![1, 1]); } // dummy
    let total = 4 * n_internal;
    let mut p = Vec::with_capacity(total - 1);
    // Vertex labels: 1..=n_internal are internal (root is 1), then 3 leaves per internal
    // Internal chain: parent of internal i (for i>=2) is internal i-1
    // Then we need to position leaves.
    // We'll reorder: create vertex order such that parent[i] appears before i.
    // Actually let's lay out: vertex 1 = root (internal_1). Then internal_2 as child of root, etc.
    // After internal n_internal, place its 3 leaves. Then internal n_internal-1's leaves, etc.
    // Simpler ordering: place all internals first, then all leaves
    // vertex i (1..=n_internal): if i==1, root; else parent = i-1
    // vertex i for i in n_internal+1 ..= 4*n_internal:
    //   leaves are grouped by internal: leaves of internal j are at positions n_internal + 3*(j-1) + 1, +2, +3
    let mut p1 = Vec::with_capacity(total - 1);
    for i in 2..=n_internal { p1.push(i - 1); }
    for j in 1..=n_internal {
        for _ in 0..3 { p1.push(j); }
    }
    p = p1;
    (total, p)
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(91301);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |n: usize, p1: Vec<usize>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if n < 3 || n > 1000 || p1.len() != n - 1 { return; }
        for (idx, &pi) in p1.iter().enumerate() {
            if pi < 1 || pi > idx + 1 { return; }
        }
        let root_children = p1.iter().filter(|&&x| x == 1).count();
        if root_children < 2 { return; }
        let key = format!("{}|{:?}", n, p1);
        if !seen.insert(key) { return; }
        let inp = build_input(n, &p1);
        let p0: Vec<usize> = p1.iter().map(|&x| x - 1).collect();
        let ans = Solution::is_spruce(n, p0);
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Boundaries
    // root with k leaves
    for k in 2..=20usize {
        let n = k + 1;
        if n > 1000 { break; }
        let p: Vec<usize> = vec![1; k];
        emit(n, p, &mut seen, &mut out, &mut count);
    }

    // Spruce trees
    for n_internal in 1..=50usize {
        let (n, p) = make_spruce(n_internal);
        if n <= 1000 {
            emit(n, p, &mut seen, &mut out, &mut count);
        }
    }

    // Trees with one node having only 2 leaves (not spruce)
    for k in 2..=20usize {
        // Root has 3 leaves + 1 sub-root
        // Sub-root has 2 leaves -> not spruce
        let n = 1 + 3 + 1 + 2;
        let p: Vec<usize> = vec![1, 1, 1, 1, 5, 5];
        let _ = k;
        emit(n, p, &mut seen, &mut out, &mut count);
        break;
    }

    while count < target {
        let n = match rng.gen_range_usize(0, 4) {
            0 => 3,
            1 => rng.gen_range_usize(4, 20),
            2 => rng.gen_range_usize(20, 100),
            _ => rng.gen_range_usize(100, 1000),
        };
        let p = make_tree(&mut rng, n);
        emit(n, p, &mut seen, &mut out, &mut count);
    }
}

