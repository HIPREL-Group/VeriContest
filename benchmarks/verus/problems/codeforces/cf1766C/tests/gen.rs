use vstd::prelude::*;

verus! {

pub fn generate_test_case(cols: Vec<u8>, mutation_kind: u8) -> (result: (usize, Vec<i64>, Vec<i64>))
    requires
        1 <= cols.len() <= 200_000,
        forall|k: int| 0 <= k < cols.len() ==> (0 <= #[trigger] cols@[k] && cols@[k] <= 2),
    ensures
        result.0 >= 1,
        result.1.len() == result.0,
        result.2.len() == result.0,
        forall |k: int| 0 <= k < result.0 as int ==> (#[trigger] result.1[k] == 0 || result.1[k] == 1),
        forall |k: int| 0 <= k < result.0 as int ==> (#[trigger] result.2[k] == 0 || result.2[k] == 1),
        forall |k: int| 0 <= k < result.0 as int ==> (#[trigger] result.1[k] == 1 || result.2[k] == 1),
{
    let mut c = cols;

    if mutation_kind == 1 {
        // set first column to "top only"
        c.set(0, 0u8);
    } else if mutation_kind == 2 {
        // set first column to "bottom only"
        c.set(0, 1u8);
    } else if mutation_kind == 3 {
        // set first column to "both"
        c.set(0, 2u8);
    } else if mutation_kind == 4 && c.len() >= 2 {
        // swap first two columns
        let a = c[0];
        let b = c[1];
        c.set(0, b);
        c.set(1, a);
    } else if mutation_kind == 5 && c.len() < 200_000 {
        // grow by one column (both black)
        c.push(2u8);
    } else if mutation_kind == 6 && c.len() > 1 {
        // shrink by one column
        c.pop();
    } else if mutation_kind == 7 {
        // set last column to "top only"
        let last = c.len() - 1;
        c.set(last, 0u8);
    } else if mutation_kind == 8 {
        // set last column to "bottom only"
        let last = c.len() - 1;
        c.set(last, 1u8);
    }

    // Build row0 and row1 from column types:
    //   0 → row0=1, row1=0 (top only)
    //   1 → row0=0, row1=1 (bottom only)
    //   2 → row0=1, row1=1 (both)
    let m = c.len();
    let mut row0: Vec<i64> = Vec::new();
    let mut row1: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant
            0 <= i <= m,
            m == c.len(),
            1 <= m <= 200_000,
            row0.len() == i,
            row1.len() == i,
            forall|k: int| 0 <= k < m as int ==> (0 <= #[trigger] c@[k] && c@[k] <= 2),
            forall|k: int| 0 <= k < i as int ==> (#[trigger] row0@[k] == 0 || row0@[k] == 1),
            forall|k: int| 0 <= k < i as int ==> (#[trigger] row1@[k] == 0 || row1@[k] == 1),
            forall|k: int| 0 <= k < i as int ==> (#[trigger] row0@[k] == 1 || row1@[k] == 1),
        decreases m - i,
    {
        if c[i] == 0 {
            row0.push(1i64);
            row1.push(0i64);
        } else if c[i] == 1 {
            row0.push(0i64);
            row1.push(1i64);
        } else {
            row0.push(1i64);
            row1.push(1i64);
        }
        i = i + 1;
    }
    (m, row0, row1)
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

// (m, row0_str, row1_str)
type TC = (usize, String, String);

fn build_input(cases: &[TC]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (m, r0, r1) in cases {
        s.push_str(&format!("{}\n{}\n{}\n", m, r0, r1));
    }
    s
}

fn build_output(cases: &[TC]) -> String {
    let mut s = String::new();
    for (m, r0, r1) in cases {
        let row0: Vec<i64> = r0.as_bytes().iter().map(|&b| if b == b'B' { 1 } else { 0 }).collect();
        let row1: Vec<i64> = r1.as_bytes().iter().map(|&b| if b == b'B' { 1 } else { 0 }).collect();
        let ans = Solution::can_paint_wall(*m, row0, row1);
        s.push_str(if ans { "YES\n" } else { "NO\n" });
    }
    s
}

// Generate two rows, each of length m, satisfying that for each j at least one of (r0[j], r1[j]) is B
fn random_case(rng: &mut Rng, m: usize) -> TC {
    let mut r0 = String::with_capacity(m);
    let mut r1 = String::with_capacity(m);
    for _ in 0..m {
        let mode = rng.gen_range_usize(0, 2);  // 0: B in r0 only; 1: B in r1 only; 2: B in both
        match mode {
            0 => { r0.push('B'); r1.push('W'); }
            1 => { r0.push('W'); r1.push('B'); }
            _ => { r0.push('B'); r1.push('B'); }
        }
    }
    (m, r0, r1)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1766);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let examples: Vec<TC> = vec![
        (3, "BBB".to_string(), "BWB".to_string()),
        (1, "B".to_string(), "B".to_string()),
        (1, "B".to_string(), "W".to_string()),
        (2, "BB".to_string(), "WW".to_string()),
        (5, "BBBBB".to_string(), "BBBBB".to_string()),
        (5, "BWBWB".to_string(), "WBWBW".to_string()),
        (4, "BWBB".to_string(), "BBWB".to_string()),
    ];

    for ex in &examples {
        if count >= target { break; }
        let cases = vec![ex.clone()];
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }

    while count < target {
        let t: usize = if count < 20 { rng.gen_range_usize(1, 5) } else { rng.gen_range_usize(2, 30) };
        let mut cases: Vec<TC> = Vec::new();
        for _ in 0..t {
            let m = match rng.gen_range_usize(0, 4) {
                0 => rng.gen_range_usize(1, 5),
                1 => rng.gen_range_usize(2, 20),
                2 => rng.gen_range_usize(20, 100),
                _ => rng.gen_range_usize(1, 50),
            };
            cases.push(random_case(&mut rng, m));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

