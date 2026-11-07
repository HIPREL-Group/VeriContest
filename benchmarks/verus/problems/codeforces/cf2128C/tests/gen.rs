use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    b: Vec<i64>,
    mutation_kind: u8,
) -> (result: (usize, Vec<i64>))
    requires
        2 <= b.len() <= 200000,
        forall|i: int| 0 <= i < b.len() ==> 1 <= #[trigger] b[i] <= 1000000000,
    ensures
        2 <= result.0 <= 200000,
        result.0 == result.1.len(),
        forall|i: int| 0 <= i < result.0 ==> 1 <= #[trigger] result.1[i] <= 1000000000,
{
    let n = b.len();
    if mutation_kind == 0 {
        // identity
        (n, b)
    } else if mutation_kind == 1 {
        // set last element to 1 (min boundary)
        let mut r = b;
        let last = r.len() - 1;
        r.set(last, 1);
        (n, r)
    } else if mutation_kind == 2 {
        // set last element to 1_000_000_000 (max boundary)
        let mut r = b;
        let last = r.len() - 1;
        r.set(last, 1_000_000_000);
        (n, r)
    } else if mutation_kind == 3 {
        // set first element to 1
        let mut r = b;
        r.set(0, 1);
        (n, r)
    } else if mutation_kind == 4 {
        // set first element to 1_000_000_000
        let mut r = b;
        r.set(0, 1_000_000_000);
        (n, r)
    } else if mutation_kind == 5 && b.len() < 200000 {
        // grow by one element (push 1)
        let mut r = b;
        r.push(1);
        let new_n = r.len();
        (new_n, r)
    } else if mutation_kind == 6 && b.len() > 2 {
        // shrink by one element
        let mut r = b;
        r.pop();
        let new_n = r.len();
        (new_n, r)
    } else if mutation_kind == 7 {
        // set all elements to 1
        let mut r = b;
        let mut i: usize = 0;
        while i < r.len()
            invariant
                0 <= i <= r.len(),
                r.len() == b.len(),
                2 <= r.len() <= 200000,
                forall|j: int| 0 <= j < i ==> r[j] == 1i64,
                forall|j: int| i <= j < r.len() ==> r[j] == b[j],
            decreases r.len() - i,
        {
            r.set(i, 1);
            i += 1;
        }
        (n, r)
    } else if mutation_kind == 8 {
        // set all elements to 1_000_000_000
        let mut r = b;
        let mut i: usize = 0;
        while i < r.len()
            invariant
                0 <= i <= r.len(),
                r.len() == b.len(),
                2 <= r.len() <= 200000,
                forall|j: int| 0 <= j < i ==> r[j] == 1_000_000_000i64,
                forall|j: int| i <= j < r.len() ==> r[j] == b[j],
            decreases r.len() - i,
        {
            r.set(i, 1_000_000_000);
            i += 1;
        }
        (n, r)
    } else if mutation_kind == 9 && b[0] < 1_000_000_000 {
        // nudge first element up
        let mut r = b;
        r.set(0, r[0] + 1);
        (n, r)
    } else if mutation_kind == 10 && b[0] > 1 {
        // nudge first element down
        let mut r = b;
        r.set(0, r[0] - 1);
        (n, r)
    } else if mutation_kind == 11 && b.len() >= 2 && b[b.len() - 1 as usize] < 1_000_000_000 {
        // nudge last element up
        let mut r = b;
        let last = r.len() - 1;
        r.set(last, r[last] + 1);
        (n, r)
    } else if mutation_kind == 12 && b.len() >= 2 && b[b.len() - 1 as usize] > 1 {
        // nudge last element down
        let mut r = b;
        let last = r.len() - 1;
        r.set(last, r[last] - 1);
        (n, r)
    } else {
        // fallback: identity
        (n, b)
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

fn build_input_multi(cases: &[Vec<i64>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for b in cases {
        s.push_str(&format!("{}\n", b.len()));
        let parts: Vec<String> = b.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output_multi(answers: &[bool]) -> String {
    let mut s = String::new();
    for &a in answers {
        s.push_str(if a { "YES\n" } else { "NO\n" });
    }
    s
}

fn solve(b: &[i64]) -> bool {
    Solution::leftmost_below(b.len(), b.to_vec())
}

fn random_case(rng: &mut Rng, mode: usize) -> Vec<i64> {
    let n = match mode {
        0 => rng.gen_range_usize(2, 5),
        1 => rng.gen_range_usize(6, 20),
        2 => rng.gen_range_usize(21, 100),
        3 => rng.gen_range_usize(101, 500),
        _ => rng.gen_range_usize(2, 50),
    };
    let max = match mode % 3 {
        0 => 100i64,
        1 => 10_000i64,
        _ => 1_000_000_000i64,
    };
    (0..n).map(|_| rng.gen_range_i64(1, max)).collect()
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(2128);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let examples: Vec<Vec<i64>> = vec![
        vec![5, 6, 1, 1],
        vec![3, 1, 2],
        vec![40, 60, 90, 21],
        vec![1, 1],
    ];
    {
        let answers: Vec<bool> = examples.iter().map(|c| solve(c)).collect();
        let inp = build_input_multi(&examples);
        let outp = build_output_multi(&answers);
        if seen.insert(inp.clone()) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }

    for ex in &examples {
        if count >= target { break; }
        let cases = vec![ex.clone()];
        let answers: Vec<bool> = cases.iter().map(|c| solve(c)).collect();
        let inp = build_input_multi(&cases);
        let outp = build_output_multi(&answers);
        if seen.insert(inp.clone()) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }

    let edges: Vec<Vec<i64>> = vec![
        vec![1, 1],
        vec![2, 1],
        vec![1, 2],
        vec![1_000_000_000, 1],
        vec![1, 1_000_000_000],
        vec![1, 2, 3, 4, 5],
        vec![5, 4, 3, 2, 1],
        vec![100, 50, 25, 10, 1],
    ];
    for chunk in edges.chunks(3) {
        if count >= target { break; }
        let cases: Vec<Vec<i64>> = chunk.to_vec();
        let answers: Vec<bool> = cases.iter().map(|c| solve(c)).collect();
        let inp = build_input_multi(&cases);
        let outp = build_output_multi(&answers);
        if seen.insert(inp.clone()) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }

    while count < target {
        let t: usize = if count < 30 { rng.gen_range_usize(1, 5) } else { rng.gen_range_usize(2, 30) };
        let mut cases: Vec<Vec<i64>> = Vec::with_capacity(t);
        for _ in 0..t {
            let mode = rng.gen_range_usize(0, 4);
            cases.push(random_case(&mut rng, mode));
        }
        let answers: Vec<bool> = cases.iter().map(|c| solve(c)).collect();
        let inp = build_input_multi(&cases);
        let outp = build_output_multi(&answers);
        if !seen.insert(inp.clone()) { continue; }
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

