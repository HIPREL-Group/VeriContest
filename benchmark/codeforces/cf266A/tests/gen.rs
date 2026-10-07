use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    // Construction parameters: raw color values and desired length
    raw_colors: Vec<u8>,
    mutation_kind: u8,
) -> (result: (Vec<u8>, usize))
    requires
        1 <= raw_colors.len() <= 50,
        forall|i: int| 0 <= i < raw_colors.len() ==> 0 <= #[trigger] raw_colors[i] as int <= 2,
    ensures
        1 <= result.1 <= 50,
        result.0.len() == result.1,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] as int <= 2,
{
    let n = raw_colors.len();
    if mutation_kind == 0 {
        // identity
        (raw_colors, n)
    } else if mutation_kind == 1 {
        // set all elements to 0 (all same color — maximum removals)
        let mut d = raw_colors;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == n,
                1 <= n <= 50,
                forall|j: int| 0 <= j < i ==> d[j] == 0u8,
                forall|j: int| i <= j < d.len() ==> 0 <= #[trigger] d[j] as int <= 2,
            decreases d.len() - i,
        {
            d.set(i, 0u8);
            i += 1;
        }
        (d, n)
    } else if mutation_kind == 2 {
        // alternating pattern: 0, 1, 0, 1, ... (zero removals)
        let mut d = raw_colors;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == n,
                1 <= n <= 50,
                forall|j: int| 0 <= j < i ==> 0 <= #[trigger] d[j] as int <= 2,
                forall|j: int| i <= j < d.len() ==> 0 <= #[trigger] d[j] as int <= 2,
            decreases d.len() - i,
        {
            if i % 2 == 0 {
                d.set(i, 0u8);
            } else {
                d.set(i, 1u8);
            }
            i += 1;
        }
        (d, n)
    } else if mutation_kind == 3 && raw_colors.len() > 1 {
        // shrink by one (pop last element)
        let mut d = raw_colors;
        d.pop();
        let new_n = d.len();
        (d, new_n)
    } else if mutation_kind == 4 && raw_colors.len() < 50 {
        // grow by one (push color 0)
        let mut d = raw_colors;
        d.push(0u8);
        let new_n = d.len();
        (d, new_n)
    } else if mutation_kind == 5 {
        // set first element to 2
        let mut d = raw_colors;
        d.set(0, 2u8);
        (d, n)
    } else if mutation_kind == 6 {
        // set last element to match first (creates at least boundary adjacency)
        let mut d = raw_colors;
        let last = d.len() - 1;
        let first_val = d[0];
        d.set(last, first_val);
        (d, n)
    } else if mutation_kind == 7 {
        // cycling pattern: 0, 1, 2, 0, 1, 2, ... (zero removals)
        let mut d = raw_colors;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == n,
                1 <= n <= 50,
                forall|j: int| 0 <= j < i ==> 0 <= #[trigger] d[j] as int <= 2,
                forall|j: int| i <= j < d.len() ==> 0 <= #[trigger] d[j] as int <= 2,
            decreases d.len() - i,
        {
            if i % 3 == 0 {
                d.set(i, 0u8);
            } else if i % 3 == 1 {
                d.set(i, 1u8);
            } else {
                d.set(i, 2u8);
            }
            i += 1;
        }
        (d, n)
    } else {
        // fallback: identity
        (raw_colors, n)
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

fn build_input(s: &str) -> String {
    format!("{}\n{}\n", s.len(), s)
}

fn build_output(ans: usize) -> String {
    format!("{}\n", ans)
}

fn solve_str(s: &str) -> usize {
    let colors: Vec<u8> = s.bytes().map(|b| match b {
        b'R' => 0u8, b'G' => 1u8, b'B' => 2u8, _ => 0u8,
    }).collect();
    Solution::min_stones_to_remove(colors, s.len())
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(266);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let examples = vec!["RRG", "RRRRR", "RGB", "R", "RG", "GG"];
    for ex in &examples {
        if count >= target { break; }
        let inp = build_input(ex);
        if !seen.insert(inp.clone()) { continue; }
        let ans = solve_str(ex);
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    let chars = ['R', 'G', 'B'];
    let mut tries = 0;
    while count < target && tries < target * 100 {
        tries += 1;
        let n = match tries % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(10, 25),
            3 => rng.gen_range_usize(25, 40),
            _ => rng.gen_range_usize(40, 50),
        };
        let s: String = (0..n).map(|_| chars[(rng.next_u64() as usize) % 3]).collect();
        let inp = build_input(&s);
        if !seen.insert(inp.clone()) { continue; }
        let ans = solve_str(&s);
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

