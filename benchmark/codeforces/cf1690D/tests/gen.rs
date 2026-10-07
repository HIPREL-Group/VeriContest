use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    len: usize,
    k_val: usize,
    cells: Vec<i64>,
    mutation_kind: u8,
) -> (result: (usize, usize, Vec<i64>))
    requires
        1 <= len,
        len <= 200000,
        1 <= k_val <= len,
        cells.len() == len,
        forall|i: int| 0 <= i < len as int ==> (#[trigger] cells[i] == 0 || cells[i] == 1),
    ensures
        1 <= result.0,
        result.0 <= 200000,
        1 <= result.1 <= result.0,
        result.2.len() == result.0,
        forall|i: int| 0 <= i < result.0 as int ==> (#[trigger] result.2@[i] == 0 || result.2@[i] == 1),
{
    if mutation_kind == 0 {
        // identity
        (len, k_val, cells)
    } else if mutation_kind == 1 {
        // set all cells to 0 (all black)
        let mut s = cells;
        let mut i: usize = 0;
        while i < len
            invariant
                s.len() == len,
                0 <= i <= len,
                1 <= len <= 200000,
                1 <= k_val <= len,
                forall|j: int| 0 <= j < i as int ==> s[j] == 0,
                forall|j: int| i as int <= j < len as int ==> (#[trigger] s[j] == 0 || s[j] == 1),
            decreases len - i,
        {
            s.set(i, 0);
            i += 1;
        }
        (len, k_val, s)
    } else if mutation_kind == 2 {
        // set all cells to 1 (all white)
        let mut s = cells;
        let mut i: usize = 0;
        while i < len
            invariant
                s.len() == len,
                0 <= i <= len,
                1 <= len <= 200000,
                1 <= k_val <= len,
                forall|j: int| 0 <= j < i as int ==> s[j] == 1,
                forall|j: int| i as int <= j < len as int ==> (#[trigger] s[j] == 0 || s[j] == 1),
            decreases len - i,
        {
            s.set(i, 1);
            i += 1;
        }
        (len, k_val, s)
    } else if mutation_kind == 3 && k_val < len {
        // increase k by 1
        (len, k_val + 1, cells)
    } else if mutation_kind == 4 && k_val > 1 {
        // decrease k by 1
        (len, k_val - 1, cells)
    } else if mutation_kind == 5 && len > 1 {
        // flip first cell
        let mut s = cells;
        let new_val: i64 = if s[0] == 0 { 1 } else { 0 };
        s.set(0, new_val);
        (len, k_val, s)
    } else if mutation_kind == 6 {
        // flip last cell
        let mut s = cells;
        let last = len - 1;
        let new_val: i64 = if s[last] == 0 { 1 } else { 0 };
        s.set(last, new_val);
        (len, k_val, s)
    } else if mutation_kind == 7 && k_val == 1 {
        // set k to n (full window)
        (len, len, cells)
    } else {
        // fallback: identity
        (len, k_val, cells)
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

fn cells_to_string(cells: &[i64]) -> String {
    let mut s = String::with_capacity(cells.len());
    for &c in cells {
        if c == 1 { s.push('W'); } else { s.push('B'); }
    }
    s
}

fn build_input(cases: &[(usize, usize, Vec<i64>)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (n, k, cells) in cases {
        s.push_str(&format!("{} {}\n", n, k));
        s.push_str(&cells_to_string(cells));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[usize]) -> String {
    let mut s = String::new();
    for a in answers {
        s.push_str(&format!("{}\n", a));
    }
    s
}

fn random_cells(rng: &mut Rng, n: usize) -> Vec<i64> {
    (0..n).map(|_| rng.gen_range_i64(0, 1)).collect()
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1690);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let examples: Vec<(usize, usize, Vec<i64>)> = vec![
        (8, 3, vec![1, 0, 0, 1, 0, 0, 0, 1]),
        (4, 2, vec![0, 0, 0, 0]),
        (5, 3, vec![0, 0, 0, 0, 0]),
        (8, 2, vec![0, 1, 0, 0, 1, 0, 1, 1]),
        (1, 1, vec![0]),
        (1, 1, vec![1]),
        (2, 1, vec![0, 1]),
        (2, 2, vec![1, 1]),
        (3, 2, vec![1, 0, 1]),
        (5, 2, vec![1, 1, 1, 1, 1]),
    ];

    // Bundle examples as single-test entries
    for ex in &examples {
        if count >= target { break; }
        let cases = vec![ex.clone()];
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let mut answers = Vec::new();
        for (n, k, s) in &cases {
            answers.push(Solution::min_recolors(*n, *k, s.clone()));
        }
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }

    // Multi-test bundled entries
    while count < target {
        let t: usize = if count < 20 { rng.gen_range_usize(1, 5) } else { rng.gen_range_usize(2, 30) };
        let mut cases: Vec<(usize, usize, Vec<i64>)> = Vec::new();
        let mut answers: Vec<usize> = Vec::new();
        for _ in 0..t {
            let n: usize = match rng.gen_range_usize(0, 4) {
                0 => rng.gen_range_usize(1, 5),
                1 => rng.gen_range_usize(1, 20),
                2 => rng.gen_range_usize(20, 100),
                3 => rng.gen_range_usize(50, 300),
                _ => rng.gen_range_usize(1, 50),
            };
            let k = rng.gen_range_usize(1, n);
            let cells = random_cells(&mut rng, n);
            let ans = Solution::min_recolors(n, k, cells.clone());
            cases.push((n, k, cells));
            answers.push(ans);
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

