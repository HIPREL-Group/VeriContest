use vstd::prelude::*;

verus! {

pub fn generate_test_case(s: Vec<i64>, mutation_kind: u8) -> (result: (usize, Vec<i64>))
    requires
        1 <= s.len() <= 2000,
        forall|i: int| 0 <= i < s.len() ==> (#[trigger] s[i] == 0 || s[i] == 1),
    ensures
        result.0 >= 1,
        result.1.len() == result.0,
        forall|i: int| 0 <= i < result.0 as int ==> (#[trigger] result.1@[i] == 0 || result.1@[i] == 1),
{
    let n = s.len();

    if mutation_kind == 0 {
        // Identity
        (n, s)
    } else if mutation_kind == 1 {
        // Flip last element
        let mut r = s;
        let last = r.len() - 1;
        let v = if r[last] == 0 { 1i64 } else { 0i64 };
        r.set(last, v);
        (n, r)
    } else if mutation_kind == 2 {
        // Flip first element
        let mut r = s;
        let v = if r[0] == 0 { 1i64 } else { 0i64 };
        r.set(0, v);
        (n, r)
    } else if mutation_kind == 3 {
        // Set all to 0
        let mut r = s;
        let mut i: usize = 0;
        while i < r.len()
            invariant
                0 <= i <= r.len(),
                r.len() == n,
                1 <= r.len() <= 2000,
                forall|j: int| 0 <= j < i ==> r[j] == 0i64,
                forall|j: int| i <= j < r.len() ==> (r[j] == 0i64 || r[j] == 1i64),
            decreases r.len() - i,
        {
            r.set(i, 0);
            i += 1;
        }
        (n, r)
    } else if mutation_kind == 4 {
        // Set all to 1
        let mut r = s;
        let mut i: usize = 0;
        while i < r.len()
            invariant
                0 <= i <= r.len(),
                r.len() == n,
                1 <= r.len() <= 2000,
                forall|j: int| 0 <= j < i ==> r[j] == 1i64,
                forall|j: int| i <= j < r.len() ==> (r[j] == 0i64 || r[j] == 1i64),
            decreases r.len() - i,
        {
            r.set(i, 1);
            i += 1;
        }
        (n, r)
    } else if mutation_kind == 5 && s.len() < 2000 {
        // Grow: push 0
        let mut r = s;
        r.push(0);
        (n + 1, r)
    } else if mutation_kind == 6 && s.len() < 2000 {
        // Grow: push 1
        let mut r = s;
        r.push(1);
        (n + 1, r)
    } else if mutation_kind == 7 && s.len() > 1 {
        // Shrink: pop
        let mut r = s;
        r.pop();
        (n - 1, r)
    } else {
        // Fallback: identity
        (n, s)
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

// (n, s_string)
type TC = (usize, String);

fn build_input(cases: &[TC]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (n, st) in cases {
        s.push_str(&format!("{}\n{}\n", n, st));
    }
    s
}

fn build_output(cases: &[TC]) -> String {
    let mut s = String::new();
    for (n, st) in cases {
        let v: Vec<i64> = st.as_bytes().iter().map(|&b| (b - b'0') as i64).collect();
        let ans = Solution::shortest_original(*n, v);
        s.push_str(&format!("{}\n", ans));
    }
    s
}

fn random_case(rng: &mut Rng, max_n: usize) -> TC {
    let n = rng.gen_range_usize(1, max_n);
    let s: String = (0..n).map(|_| if rng.next_u64() % 2 == 0 { '0' } else { '1' }).collect();
    (n, s)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1791);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let examples: Vec<TC> = vec![
        (3, "100".to_string()),
        (4, "0111".to_string()),
        (5, "10101".to_string()),
        (6, "101010".to_string()),
        (7, "1010110".to_string()),
        (10, "1100110010".to_string()),
        (1, "0".to_string()),
        (1, "1".to_string()),
        (2, "01".to_string()),
        (2, "10".to_string()),
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
            let max_n = match rng.gen_range_usize(0, 4) {
                0 => 5,
                1 => 30,
                2 => 200,
                3 => 1000,
                _ => 100,
            };
            cases.push(random_case(&mut rng, max_n));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

