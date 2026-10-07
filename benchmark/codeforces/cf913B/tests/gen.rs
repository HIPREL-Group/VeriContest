use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    max_parent: usize,
    mutation_kind: u8,
) -> (result: (usize, Vec<usize>))
    requires
        3 <= n <= 1000,
    ensures
        result.0 >= 3,
        result.0 <= 1000,
        result.1.len() == result.0 - 1,
        forall|i: int| 0 <= i && i < result.1.len() ==> result.1@[i] <= i as usize,
{
    let mut p: Vec<usize> = Vec::new();
    let mut idx: usize = 0;

    if mutation_kind == 0 {
        // Controlled-width tree: parent is min(max_parent, idx)
        while idx < n - 1
            invariant
                n >= 3,
                n <= 1000,
                idx <= n - 1,
                p.len() == idx,
                forall|j: int| 0 <= j < idx as int ==> p@[j] <= j as usize,
            decreases n - 1 - idx,
        {
            let parent = if max_parent <= idx { max_parent } else { idx };
            p.push(parent);
            idx = idx + 1;
        }
    } else if mutation_kind == 1 {
        // Chain tree: each node's parent is the previous node
        while idx < n - 1
            invariant
                n >= 3,
                n <= 1000,
                idx <= n - 1,
                p.len() == idx,
                forall|j: int| 0 <= j < idx as int ==> p@[j] <= j as usize,
            decreases n - 1 - idx,
        {
            p.push(idx);
            idx = idx + 1;
        }
    } else if mutation_kind == 2 {
        // Binary tree: parent is floor(idx / 2)
        while idx < n - 1
            invariant
                n >= 3,
                n <= 1000,
                idx <= n - 1,
                p.len() == idx,
                forall|j: int| 0 <= j < idx as int ==> p@[j] <= j as usize,
            decreases n - 1 - idx,
        {
            p.push(idx / 2);
            idx = idx + 1;
        }
    } else {
        // Star tree: all nodes are children of root
        while idx < n - 1
            invariant
                n >= 3,
                n <= 1000,
                idx <= n - 1,
                p.len() == idx,
                forall|j: int| 0 <= j < idx as int ==> p@[j] <= j as usize,
            decreases n - 1 - idx,
        {
            p.push(0usize);
            idx = idx + 1;
        }
    }

    (n, p)
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

// p_one_indexed: parent of vertex i+2 is p_one_indexed[i] (1-indexed)
fn build_input(n: usize, p_one_indexed: &[usize]) -> String {
    let mut s = format!("{}\n", n);
    for &pi in p_one_indexed { s.push_str(&format!("{}\n", pi)); }
    s
}

fn build_output(yes: bool) -> String { if yes { "Yes\n".into() } else { "No\n".into() } }

// Build a random rooted tree of n>=3 vertices where root (1) has >=2 children.
fn make_tree(rng: &mut Rng, n: usize) -> Vec<usize> {
    // Generate p such that p[i] in 1..=i (where i is 1-indexed = vertex i+1's parent)
    // For root to have >=2 children, ensure at least two p[i] equal 1
    if n < 3 { return Vec::new(); }
    let mut p = Vec::with_capacity(n - 1);
    // first two vertices (vertex 2 and 3) point to root
    p.push(1);
    p.push(1);
    for i in 3..n {
        // vertex i+1's parent in 1..=i
        let par = rng.gen_range_usize(1, i);
        p.push(par);
    }
    p
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(913);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |n: usize, p1: Vec<usize>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if n < 3 || n > 1000 || p1.len() != n - 1 { return; }
        for (idx, &pi) in p1.iter().enumerate() {
            if pi < 1 || pi > idx + 1 { return; }
        }
        // Root must have >= 2 children
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

    // Examples
    emit(4, vec![1, 1, 1], &mut seen, &mut out, &mut count);
    emit(7, vec![1, 1, 1, 2, 2, 2], &mut seen, &mut out, &mut count);
    emit(8, vec![1, 1, 1, 1, 3, 3, 3], &mut seen, &mut out, &mut count);

    // Edges
    emit(3, vec![1, 1], &mut seen, &mut out, &mut count); // root with 2 leaves -> not spruce since needs 3
    emit(5, vec![1, 1, 1, 1], &mut seen, &mut out, &mut count); // 4 leaves, spruce
    emit(4, vec![1, 1, 2], &mut seen, &mut out, &mut count); // root has 2 leaf children -> No
    emit(10, vec![1, 1, 1, 1, 1, 1, 1, 1, 1], &mut seen, &mut out, &mut count); // root with 9 leaves

    while count < target {
        let n = rng.gen_range_usize(3, 50);
        let p = make_tree(&mut rng, n);
        emit(n, p, &mut seen, &mut out, &mut count);
    }
}

