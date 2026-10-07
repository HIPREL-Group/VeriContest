use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    choices: Vec<i32>,
    mutation_kind: u8,
) -> (result: Vec<i32>)
    requires
        1 <= choices.len() <= 200_000,
    ensures
        1 <= result.len() <= 200_000,
        forall|k: int|
            0 <= k < result.len() as int ==> #[trigger] result[k] == 0 || result[k] == 1,
        forall|k: int|
            0 <= k < result.len() as int - 1 ==> !(#[trigger] result[k] == 1 && result[k + 1] == 1),
{
    let len = choices.len();
    let mut s: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            s.len() == i,
            len == choices.len(),
            1 <= len <= 200_000,
            forall|k: int| 0 <= k < i as int ==> #[trigger] s@[k] == 0 || s@[k] == 1,
            forall|k: int|
                0 <= k < i as int - 1 ==> !(#[trigger] s@[k] == 1 && s@[k + 1] == 1),
        decreases len - i,
    {
        let prev_is_one: bool = if i > 0 { s[i - 1] == 1 } else { false };
        if choices[i] > 0 && !prev_is_one {
            s.push(1);
        } else {
            s.push(0);
        }
        i += 1;
    }

    if mutation_kind == 0 {
        // identity
        s
    } else if mutation_kind == 1 {
        // set first element to 0 (removing a 1 is always safe)
        s.set(0, 0);
        s
    } else if mutation_kind == 2 {
        // set last element to 0
        s.set(len - 1, 0);
        s
    } else if mutation_kind == 3 && len >= 2 && s[1] == 0 {
        // set first element to 1 (safe since s[1] == 0)
        s.set(0, 1);
        s
    } else if mutation_kind == 4 && len >= 2 && s[len - 2] == 0 {
        // set last element to 1 (safe since s[len-2] == 0)
        s.set(len - 1, 1);
        s
    } else {
        // fallback: identity
        s
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

fn build_input_multi(cases: &[Vec<i32>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for c in cases {
        s.push_str(&format!("{}\n", c.len()));
        for &v in c {
            s.push(if v == 1 { '1' } else { '0' });
        }
        s.push('\n');
    }
    s
}

fn build_output_multi(answers: &[i64]) -> String {
    let mut s = String::new();
    for &a in answers {
        s.push_str(&format!("{}\n", a));
    }
    s
}

fn solve(s: &Vec<i32>) -> i64 {
    Solution::min_total_seated_students(s)
}

fn random_valid(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = vec![0; n];
    let mut i = 0;
    while i < n {
        if rng.next_u64() % 3 == 0 {
            v[i] = 1;
            i += 2;
        } else {
            i += 1;
        }
    }
    v
}

fn random_case(rng: &mut Rng, mode: usize) -> Vec<i32> {
    let n = match mode {
        0 => rng.gen_range_usize(1, 5),
        1 => rng.gen_range_usize(6, 20),
        2 => rng.gen_range_usize(21, 100),
        3 => rng.gen_range_usize(101, 500),
        4 => rng.gen_range_usize(501, 1000),
        _ => rng.gen_range_usize(1, 100),
    };
    random_valid(rng, n)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(2188);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let examples: Vec<Vec<i32>> = vec![
        vec![0],
        vec![0, 0, 0],
        vec![0, 0, 0, 0, 0],
        vec![1, 0, 0, 1, 0, 1],
        vec![0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0],
    ];
    {
        let answers: Vec<i64> = examples.iter().map(|c| solve(c)).collect();
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
        let answers: Vec<i64> = cases.iter().map(|c| solve(c)).collect();
        let inp = build_input_multi(&cases);
        let outp = build_output_multi(&answers);
        if seen.insert(inp.clone()) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }

    let edges: Vec<Vec<i32>> = vec![
        vec![1],
        vec![0],
        vec![0, 1],
        vec![1, 0],
        vec![1, 0, 1],
        vec![0, 0, 0, 0],
        vec![1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        vec![1, 0, 1, 0, 1, 0, 1],
    ];
    for chunk in edges.chunks(3) {
        if count >= target { break; }
        let cases: Vec<Vec<i32>> = chunk.to_vec();
        let answers: Vec<i64> = cases.iter().map(|c| solve(c)).collect();
        let inp = build_input_multi(&cases);
        let outp = build_output_multi(&answers);
        if seen.insert(inp.clone()) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }

    while count < target {
        let t: usize = if count < 30 { rng.gen_range_usize(1, 5) } else { rng.gen_range_usize(2, 30) };
        let mut cases: Vec<Vec<i32>> = Vec::with_capacity(t);
        for _ in 0..t {
            let mode = rng.gen_range_usize(0, 4);
            cases.push(random_case(&mut rng, mode));
        }
        let answers: Vec<i64> = cases.iter().map(|c| solve(c)).collect();
        let inp = build_input_multi(&cases);
        let outp = build_output_multi(&answers);
        if !seen.insert(inp.clone()) { continue; }
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

