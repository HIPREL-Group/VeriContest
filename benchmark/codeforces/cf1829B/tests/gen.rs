use vstd::prelude::*;

verus! {

pub fn generate_test_case(a: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= a.len() <= 100,
        forall|j: int| 0 <= j < a.len() ==> #[trigger] a[j] == 0 || a[j] == 1,
    ensures
        1 <= result.len() && result.len() <= 100,
        forall|j: int| 0 <= j < result.len() ==> #[trigger] result[j] == 0 || result[j] == 1,
{
    if mutation_kind == 0 {
        // identity
        a
    } else if mutation_kind == 1 {
        // set last element to 0
        let mut r = a;
        let last = r.len() - 1;
        r.set(last, 0);
        r
    } else if mutation_kind == 2 {
        // set last element to 1
        let mut r = a;
        let last = r.len() - 1;
        r.set(last, 1);
        r
    } else if mutation_kind == 3 {
        // set first element to 0
        let mut r = a;
        r.set(0, 0);
        r
    } else if mutation_kind == 4 {
        // set first element to 1
        let mut r = a;
        r.set(0, 1);
        r
    } else if mutation_kind == 5 && a.len() < 100 {
        // grow by one element (push 0)
        let mut r = a;
        r.push(0);
        r
    } else if mutation_kind == 6 && a.len() < 100 {
        // grow by one element (push 1)
        let mut r = a;
        r.push(1);
        r
    } else if mutation_kind == 7 && a.len() > 1 {
        // shrink by one element
        let mut r = a;
        r.pop();
        r
    } else if mutation_kind == 8 {
        // set all elements to 0
        let mut r = a;
        let mut i: usize = 0;
        while i < r.len()
            invariant
                0 <= i <= r.len(),
                r.len() == a.len(),
                1 <= r.len() <= 100,
                forall|j: int| 0 <= j < i ==> r[j] == 0i32,
                forall|j: int| i <= j < r.len() ==> r[j] == a[j],
            decreases r.len() - i,
        {
            r.set(i, 0);
            i += 1;
        }
        r
    } else if mutation_kind == 9 {
        // set all elements to 1
        let mut r = a;
        let mut i: usize = 0;
        while i < r.len()
            invariant
                0 <= i <= r.len(),
                r.len() == a.len(),
                1 <= r.len() <= 100,
                forall|j: int| 0 <= j < i ==> r[j] == 1i32,
                forall|j: int| i <= j < r.len() ==> r[j] == a[j],
            decreases r.len() - i,
        {
            r.set(i, 1);
            i += 1;
        }
        r
    } else if mutation_kind == 10 {
        // flip last element
        let mut r = a;
        let last = r.len() - 1;
        if r[last] == 0 {
            r.set(last, 1);
        } else {
            r.set(last, 0);
        }
        r
    } else {
        // fallback: identity
        a
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

fn random_binary(rng: &mut Rng, len: usize, p_one: u32) -> Vec<i32> {
    (0..len).map(|_| if (rng.next_u64() % 100) < p_one as u64 {1i32} else {0}).collect()
}

fn build_input(cases: &[Vec<i32>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for a in cases {
        s.push_str(&format!("{}\n", a.len()));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[i32]) -> String {
    let mut s = String::new();
    for a in answers {
        s.push_str(&format!("{}\n", a));
    }
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1829);
    let mut seen: HashSet<String> = HashSet::new();

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // Example
    {
        let cases = vec![vec![1, 0, 0, 1, 0]];
        let answers: Vec<i32> = cases.iter().map(|a| Solution::longest_blank_space(a)).collect();
        let inp = build_input(&cases);
        let outs = build_output(&answers);
        if seen.insert(inp.clone()) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
            count += 1;
        }
    }

    // Single-test edge cases
    let edge: Vec<Vec<i32>> = vec![
        vec![0],
        vec![1],
        vec![0; 100],
        vec![1; 100],
        vec![0, 1, 0, 1],
        vec![1, 1, 0, 0, 0, 1, 1],
        vec![0, 0, 1, 0, 0, 0, 1, 0],
    ];
    for ec in &edge {
        if count >= target { break; }
        let cases = vec![ec.clone()];
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i32> = cases.iter().map(|a| Solution::longest_blank_space(a)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }

    // Bundled multi-test
    while count < target {
        let t: usize = if count < 30 { rng.gen_range_usize(2, 10) } else { rng.gen_range_usize(5, 30) };
        let mut cases: Vec<Vec<i32>> = Vec::new();
        for _ in 0..t {
            let n = rng.gen_range_usize(1, 100);
            let p = (rng.next_u64() % 90 + 5) as u32;
            cases.push(random_binary(&mut rng, n, p));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i32> = cases.iter().map(|a| Solution::longest_blank_space(a)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

