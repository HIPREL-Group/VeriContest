use vstd::prelude::*;

verus! {

pub fn generate_test_case(a: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= a.len() <= 50,
        forall|i: int| 0 <= i < a.len() as int ==> 1 <= #[trigger] a[i] as int <= 100,
    ensures
        1 <= result.len() <= 50,
        forall|i: int| 0 <= i < result.len() as int ==> 1 <= #[trigger] result[i] as int <= 100,
{
    if mutation_kind == 0 {
        // identity
        a
    } else if mutation_kind == 1 {
        // set first element to 1 (min boundary)
        let mut d = a;
        d.set(0, 1);
        d
    } else if mutation_kind == 2 {
        // set first element to 100 (max boundary)
        let mut d = a;
        d.set(0, 100);
        d
    } else if mutation_kind == 3 {
        // set all elements to 1
        let mut d = a;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == a.len(),
                1 <= d.len() <= 50,
                forall|j: int| 0 <= j < i ==> d[j] == 1i32,
                forall|j: int| i <= j < d.len() ==> d[j] == a[j],
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        d
    } else if mutation_kind == 4 {
        // set all elements to 100
        let mut d = a;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == a.len(),
                1 <= d.len() <= 50,
                forall|j: int| 0 <= j < i ==> d[j] == 100i32,
                forall|j: int| i <= j < d.len() ==> d[j] == a[j],
            decreases d.len() - i,
        {
            d.set(i, 100);
            i += 1;
        }
        d
    } else if mutation_kind == 5 && a.len() < 50 {
        // grow by one element (push 1)
        let mut d = a;
        d.push(1);
        d
    } else if mutation_kind == 6 && a.len() > 1 {
        // shrink by one element (pop)
        let mut d = a;
        d.pop();
        d
    } else if mutation_kind == 7 {
        // nudge first element up (if < 100)
        let mut d = a;
        if d[0] < 100 {
            d.set(0, d[0] + 1);
        }
        d
    } else if mutation_kind == 8 {
        // nudge first element down (if > 1)
        let mut d = a;
        if d[0] > 1 {
            d.set(0, d[0] - 1);
        }
        d
    } else if mutation_kind == 9 {
        // set last element to 1
        let mut d = a;
        let last = d.len() - 1;
        d.set(last, 1);
        d
    } else if mutation_kind == 10 {
        // set last element to 100
        let mut d = a;
        let last = d.len() - 1;
        d.set(last, 100);
        d
    } else {
        a // fallback
    }
}

}

use std::io::Write;

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let r = (hi as i64 - lo as i64 + 1) as u64;
        (lo as i64 + (self.next_u64() % r) as i64) as i32
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

fn build_output(answers: &[bool]) -> String {
    let mut s = String::new();
    for &a in answers {
        s.push_str(if a { "YES\n" } else { "NO\n" });
    }
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);

    // Examples
    {
        let cases: Vec<Vec<i32>> = vec![
            vec![1, 2, 2],
            vec![5, 5, 5, 5],
            vec![1, 2, 4],
            vec![1, 3, 4, 4],
            vec![100],
        ];
        let answers: Vec<bool> = cases.iter().map(|a| Solution::remove_smallest_possible(a.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
    }
    let mut count = 1usize;

    // edges
    let edges: Vec<Vec<i32>> = vec![
        vec![1],
        vec![100],
        vec![1, 1],
        vec![1, 2],
        vec![1, 3],
        vec![1, 100],
        vec![1, 2, 3, 4, 5],
        vec![1, 1, 1, 1],
    ];
    for e in edges {
        if count >= target { break; }
        let cases: Vec<Vec<i32>> = vec![e];
        let answers: Vec<bool> = cases.iter().map(|a| Solution::remove_smallest_possible(a.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    while count < target {
        let t: usize = if count < 20 { 1 } else { rng.gen_range_usize(2, 20) };
        let mut cases: Vec<Vec<i32>> = Vec::new();
        for _ in 0..t {
            let n = match rng.next_u64() % 4 {
                0 => 1,
                1 => rng.gen_range_usize(2, 5),
                2 => rng.gen_range_usize(5, 20),
                _ => rng.gen_range_usize(20, 50),
            };
            let mut a: Vec<i32> = Vec::with_capacity(n);
            // Mix: sometimes connected (gaps <=1), sometimes random
            let mode = rng.next_u64() % 3;
            match mode {
                0 => {
                    let mx = rng.gen_range_i32(1, 100);
                    for _ in 0..n { a.push(rng.gen_range_i32(1, mx)); }
                }
                1 => {
                    let v = rng.gen_range_i32(1, 100);
                    for _ in 0..n { a.push(v + (rng.next_u64() % 2) as i32); }
                }
                _ => {
                    for _ in 0..n { a.push(rng.gen_range_i32(1, 100)); }
                }
            }
            cases.push(a);
        }
        let answers: Vec<bool> = cases.iter().map(|a| Solution::remove_smallest_possible(a.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

