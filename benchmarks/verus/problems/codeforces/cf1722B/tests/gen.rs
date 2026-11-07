use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    raw1: Vec<u8>,
    raw2: Vec<u8>,
    mutation_kind: u8,
) -> (result: (usize, Vec<u8>, Vec<u8>))
    requires
        1 <= raw1.len() <= 100,
        raw1.len() == raw2.len(),
        forall|i: int| 0 <= i < raw1.len() ==> #[trigger] raw1[i] <= 2u8,
        forall|i: int| 0 <= i < raw2.len() ==> #[trigger] raw2[i] <= 2u8,
    ensures
        1 <= result.0 <= 100,
        result.1.len() == result.0,
        result.2.len() == result.0,
        forall|i: int| 0 <= i < result.1.len() ==> #[trigger] result.1[i] <= 2u8,
        forall|i: int| 0 <= i < result.2.len() ==> #[trigger] result.2[i] <= 2u8,
{
    let n = raw1.len();
    if mutation_kind == 0 {
        (n, raw1, raw2)
    } else if mutation_kind == 1 {
        // make rows match by setting all to 0 (R)
        let mut a = raw1;
        let mut b = raw2;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                a.len() == n,
                b.len() == n,
                1 <= n <= 100,
                forall|k: int| 0 <= k < a.len() ==> #[trigger] a[k] <= 2u8,
                forall|k: int| 0 <= k < b.len() ==> #[trigger] b[k] <= 2u8,
            decreases n - i,
        {
            a.set(i, 0u8);
            b.set(i, 0u8);
            i += 1;
        }
        (n, a, b)
    } else if mutation_kind == 2 {
        // first row all G, second all B
        let mut a = raw1;
        let mut b = raw2;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                a.len() == n,
                b.len() == n,
                1 <= n <= 100,
                forall|k: int| 0 <= k < a.len() ==> #[trigger] a[k] <= 2u8,
                forall|k: int| 0 <= k < b.len() ==> #[trigger] b[k] <= 2u8,
            decreases n - i,
        {
            a.set(i, 1u8);
            b.set(i, 2u8);
            i += 1;
        }
        (n, a, b)
    } else if mutation_kind == 3 {
        // first row all R, second all G
        let mut a = raw1;
        let mut b = raw2;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                a.len() == n,
                b.len() == n,
                1 <= n <= 100,
                forall|k: int| 0 <= k < a.len() ==> #[trigger] a[k] <= 2u8,
                forall|k: int| 0 <= k < b.len() ==> #[trigger] b[k] <= 2u8,
            decreases n - i,
        {
            a.set(i, 0u8);
            b.set(i, 1u8);
            i += 1;
        }
        (n, a, b)
    } else if mutation_kind == 4 && raw1.len() > 1 {
        let mut a = raw1;
        let mut b = raw2;
        a.pop();
        b.pop();
        let new_n = a.len();
        (new_n, a, b)
    } else {
        (n, raw1, raw2)
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

fn build_input(s1: &str, s2: &str) -> String {
    format!("1\n{}\n{}\n{}\n", s1.len(), s1, s2)
}

fn parse_row(s: &str) -> Vec<u8> {
    s.bytes().map(|b| match b {
        b'R' => 0u8, b'G' => 1u8, b'B' => 2u8, _ => 0u8,
    }).collect()
}

fn solve_str(s1: &str, s2: &str) -> bool {
    let r1 = parse_row(s1);
    let r2 = parse_row(s2);
    Solution::colourblind_match(s1.len(), r1, r2)
}

fn build_output(ans: bool) -> String {
    if ans { "YES\n".to_string() } else { "NO\n".to_string() }
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1722);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let chars = ['R', 'G', 'B'];
    let examples = vec![
        ("RG", "RB"),
        ("GRBG", "GBGB"),
        ("GGGGG", "BBBBB"),
        ("BBBBBBB", "RRRRRRR"),
        ("RGBRRGBR", "RGGRRBGR"),
        ("G", "G"),
    ];
    for (s1, s2) in &examples {
        if count >= target { break; }
        let inp = build_input(s1, s2);
        if !seen.insert(inp.clone()) { continue; }
        let ans = solve_str(s1, s2);
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    let mut tries = 0;
    while count < target && tries < target * 100 {
        tries += 1;
        let n = match tries % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(10, 25),
            3 => rng.gen_range_usize(25, 50),
            _ => rng.gen_range_usize(50, 100),
        };
        let s1: String = (0..n).map(|_| chars[(rng.next_u64() as usize) % 3]).collect();
        let s2: String = (0..n).map(|_| chars[(rng.next_u64() as usize) % 3]).collect();
        let inp = build_input(&s1, &s2);
        if !seen.insert(inp.clone()) { continue; }
        let ans = solve_str(&s1, &s2);
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
