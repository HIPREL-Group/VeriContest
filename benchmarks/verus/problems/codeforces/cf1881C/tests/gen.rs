use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n_half: usize,
    grid: Vec<i64>,
    mutation_kind: u8,
) -> (result: (usize, Vec<i64>))
    requires
        1 <= n_half <= 500,
        grid.len() == (2 * n_half as int) * (2 * n_half as int),
        forall|k: int|
            0 <= k < grid.len() ==> 0 <= (#[trigger] grid[k] as int) && (grid[k] as int) <= 25,
    ensures
        2 <= (result.0 as int) <= 1000,
        (result.0 as int) % 2 == 0,
        (result.1.len() as int) == (result.0 as int) * (result.0 as int),
        forall|k: int|
            0 <= k < (result.1.len() as int) ==> 0 <= (#[trigger] result.1[k] as int) && (result.1[k] as int) <= 25,
{
    let n: usize = 2 * n_half;

    if mutation_kind == 0 {
        // identity
        (n, grid)
    } else if mutation_kind == 1 {
        // set all values to 0
        let len = grid.len();
        let mut g = grid;
        let mut i: usize = 0;
        while i < len
            invariant
                len == g.len(),
                len == (2 * n_half as int) * (2 * n_half as int),
                0 <= i <= len,
                forall|k: int|
                    0 <= k < len ==> 0 <= (#[trigger] g[k] as int) && (g[k] as int) <= 25,
            decreases len - i,
        {
            g.set(i, 0i64);
            i = i + 1;
        }
        (n, g)
    } else if mutation_kind == 2 {
        // set all values to 25
        let len = grid.len();
        let mut g = grid;
        let mut i: usize = 0;
        while i < len
            invariant
                len == g.len(),
                len == (2 * n_half as int) * (2 * n_half as int),
                0 <= i <= len,
                forall|k: int|
                    0 <= k < len ==> 0 <= (#[trigger] g[k] as int) && (g[k] as int) <= 25,
            decreases len - i,
        {
            g.set(i, 25i64);
            i = i + 1;
        }
        (n, g)
    } else if mutation_kind == 3 && grid.len() > 0 {
        // nudge first element up (if < 25)
        let mut g = grid;
        if g[0] < 25 {
            g.set(0, g[0] + 1);
        }
        (n, g)
    } else if mutation_kind == 4 && grid.len() > 0 {
        // nudge first element down (if > 0)
        let mut g = grid;
        if g[0] > 0 {
            g.set(0, g[0] - 1);
        }
        (n, g)
    } else if mutation_kind == 5 && grid.len() > 0 {
        // set first element to 0
        let mut g = grid;
        g.set(0, 0i64);
        (n, g)
    } else if mutation_kind == 6 && grid.len() > 0 {
        // set first element to 25
        let mut g = grid;
        g.set(0, 25i64);
        (n, g)
    } else {
        // fallback: identity
        (n, grid)
    }
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

// Each case: (n, grid_strings)
type Case = (usize, Vec<String>);

fn build_input(cases: &[Case]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (n, rows) in cases {
        s.push_str(&format!("{}\n", n));
        for r in rows {
            s.push_str(r);
            s.push('\n');
        }
    }
    s
}

fn build_output(answers: &[i64]) -> String {
    let mut s = String::new();
    for a in answers { s.push_str(&format!("{}\n", a)); }
    s
}

fn solve(c: &Case) -> i64 {
    let mut grid: Vec<i64> = Vec::with_capacity(c.0 * c.0);
    for r in &c.1 {
        for ch in r.chars() {
            grid.push((ch as u8 - b'a') as i64);
        }
    }
    Solution::min_ops_perfect_square(c.0, grid)
}

fn random_case(rng: &mut Rng, n: usize) -> Case {
    let rows: Vec<String> = (0..n).map(|_| {
        let s: String = (0..n).map(|_| {
            (b'a' + (rng.gen_range_i64(0, 25) as u8)) as char
        }).collect();
        s
    }).collect();
    (n, rows)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1881);
    let mut seen: HashSet<String> = HashSet::new();

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // Example
    let example: Vec<Case> = vec![
        (4, vec!["abba".to_string(), "abcb".to_string(), "bbcc".to_string(), "babba".to_string()]),
        (2, vec!["ab".to_string(), "ba".to_string()]),
        (6, vec![
            "codefo".to_string(), "rcesco".to_string(), "deforc".to_string(),
            "escode".to_string(), "forces".to_string(), "codefo".to_string(),
        ]),
        (4, vec!["baaa".to_string(), "abba".to_string(), "baba".to_string(), "baab".to_string()]),
        (4, vec!["bbaa".to_string(), "abba".to_string(), "aaba".to_string(), "abba".to_string()]),
    ];
    // The first test case from the description has a "babba" row that's 5 chars - that's a typo. Adjust:
    let example: Vec<Case> = vec![
        (4, vec!["abba".to_string(), "abcb".to_string(), "bbcc".to_string(), "abba".to_string()]),  // -> ?
        (2, vec!["ab".to_string(), "ba".to_string()]),
        (4, vec!["baaa".to_string(), "abba".to_string(), "baba".to_string(), "baab".to_string()]),
    ];
    {
        let inp = build_input(&example);
        let answers: Vec<i64> = example.iter().map(|c| solve(c)).collect();
        let outs = build_output(&answers);
        if seen.insert(inp.clone()) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
            count += 1;
        }
    }

    // Edges
    let edges: Vec<Case> = vec![
        (2, vec!["aa".to_string(), "aa".to_string()]),  // already perfect: 0
        (2, vec!["az".to_string(), "az".to_string()]),
        (2, vec!["zz".to_string(), "zz".to_string()]),
        (4, vec!["abba".to_string(), "baab".to_string(), "baab".to_string(), "abba".to_string()]),  // perfect square
    ];
    for ec in &edges {
        if count >= target { break; }
        let cases = vec![ec.clone()];
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i64> = cases.iter().map(|c| solve(c)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }

    // Bundles
    while count < target {
        let t: usize = if count < 30 { rng.gen_range_usize(2, 5) } else { rng.gen_range_usize(3, 10) };
        let mut cases: Vec<Case> = Vec::new();
        let mut total_n = 0usize;
        for _ in 0..t {
            // pick even n in [2, 100]
            let n = (rng.gen_range_usize(1, 50)) * 2;
            if total_n + n > 1000 { break; }
            total_n += n;
            cases.push(random_case(&mut rng, n));
        }
        if cases.is_empty() { continue; }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i64> = cases.iter().map(|c| solve(c)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

