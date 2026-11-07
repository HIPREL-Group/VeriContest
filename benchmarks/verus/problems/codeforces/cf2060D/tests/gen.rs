use vstd::prelude::*;

verus! {

pub fn generate_test_case(a: Vec<i64>, mutation_kind: u8) -> (result: Vec<i64>)
    requires
        2 <= a.len() <= 200_000,
        forall|k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= 1_000_000_000,
    ensures
        2 <= result.len() <= 200_000,
        forall|k: int| 0 <= k < result.len() ==> 1 <= #[trigger] result[k] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        a
    } else if mutation_kind == 1 {
        // set last element to 1
        let mut r = a;
        let last = r.len() - 1;
        r.set(last, 1);
        r
    } else if mutation_kind == 2 {
        // set last element to max
        let mut r = a;
        let last = r.len() - 1;
        r.set(last, 1_000_000_000);
        r
    } else if mutation_kind == 3 && a[a.len() - 1] < 1_000_000_000 {
        // nudge last element up
        let mut r = a;
        let last = r.len() - 1;
        r.set(last, r[last] + 1);
        r
    } else if mutation_kind == 4 && a[a.len() - 1] > 1 {
        // nudge last element down
        let mut r = a;
        let last = r.len() - 1;
        r.set(last, r[last] - 1);
        r
    } else if mutation_kind == 5 && a.len() < 200_000 {
        // grow by one element
        let mut r = a;
        r.push(1);
        r
    } else if mutation_kind == 6 && a.len() > 2 {
        // shrink by one element
        let mut r = a;
        r.pop();
        r
    } else if mutation_kind == 7 {
        // set all elements to 1
        let mut r = a;
        let mut i: usize = 0;
        while i < r.len()
            invariant
                0 <= i <= r.len(),
                r.len() == a.len(),
                2 <= r.len() <= 200_000,
                forall|j: int| 0 <= j < i ==> r[j] == 1i64,
                forall|j: int| i <= j < r.len() ==> r[j] == a[j],
            decreases r.len() - i,
        {
            r.set(i, 1);
            i += 1;
        }
        r
    } else if mutation_kind == 8 {
        // set all elements to max
        let mut r = a;
        let mut i: usize = 0;
        while i < r.len()
            invariant
                0 <= i <= r.len(),
                r.len() == a.len(),
                2 <= r.len() <= 200_000,
                forall|j: int| 0 <= j < i ==> r[j] == 1_000_000_000i64,
                forall|j: int| i <= j < r.len() ==> r[j] == a[j],
            decreases r.len() - i,
        {
            r.set(i, 1_000_000_000);
            i += 1;
        }
        r
    } else if mutation_kind == 9 {
        // set first element to 1
        let mut r = a;
        r.set(0, 1);
        r
    } else if mutation_kind == 10 {
        // set first element to max
        let mut r = a;
        r.set(0, 1_000_000_000);
        r
    } else if mutation_kind == 11 && a.len() >= 2 {
        // swap first two elements
        let mut r = a;
        let tmp = r[0];
        r.set(0, r[1]);
        r.set(1, tmp);
        r
    } else {
        // fallback identity
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

fn build_input_multi(cases: &[Vec<i64>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for a in cases {
        s.push_str(&format!("{}\n", a.len()));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
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

fn build_mode(rng: &mut Rng, mode: usize) -> Vec<i64> {
    match mode {
        0 => {
            let n = rng.gen_range_usize(2, 10);
            let mut v = Vec::with_capacity(n);
            let mut cur: i64 = rng.gen_range_i64(1, 100);
            for _ in 0..n {
                v.push(cur);
                cur += rng.gen_range_i64(0, 10);
                if cur > 1_000_000_000 { cur = 1_000_000_000; }
            }
            v
        }
        1 => {
            let n = rng.gen_range_usize(2, 20);
            let mut v = Vec::with_capacity(n);
            let mut cur: i64 = rng.gen_range_i64(n as i64, 1_000_000);
            for _ in 0..n {
                v.push(cur);
                cur -= 1;
                if cur < 1 { cur = 1; }
            }
            v
        }
        2 => {
            let n = rng.gen_range_usize(2, 50);
            let x = rng.gen_range_i64(1, 1_000_000_000);
            vec![x; n]
        }
        3 => {
            vec![rng.gen_range_i64(1, 1_000_000_000), rng.gen_range_i64(1, 1_000_000_000)]
        }
        4 => {
            let n = rng.gen_range_usize(2, 30);
            (0..n).map(|_| rng.gen_range_i64(1, 1_000_000_000)).collect()
        }
        5 => {
            let n = rng.gen_range_usize(2, 100);
            vec![1i64; n]
        }
        6 => {
            let n = rng.gen_range_usize(2, 50);
            (0..n).map(|_| rng.gen_range_i64(1, 10)).collect()
        }
        7 => {
            let n = rng.gen_range_usize(2, 200);
            (0..n).map(|_| rng.gen_range_i64(1, 1_000_000_000)).collect()
        }
        8 => {
            let n = rng.gen_range_usize(2, 40);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(rng.gen_range_i64(1, 100));
                } else {
                    v.push(rng.gen_range_i64(500_000_000, 1_000_000_000));
                }
            }
            v
        }
        _ => {
            let n = rng.gen_range_usize(3, 20);
            let mut v = Vec::with_capacity(n);
            let a = rng.gen_range_i64(50, 1000);
            let b = rng.gen_range_i64(1, a - 1);
            v.push(a);
            v.push(a);
            for _ in 2..n {
                v.push(b);
            }
            v
        }
    }
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let examples: Vec<Vec<i64>> = vec![
        vec![1, 2, 3, 4, 5],
        vec![4, 3, 2, 1],
        vec![4, 5, 2, 3],
        vec![4, 5, 4, 5, 4, 5, 4, 5],
        vec![9, 9, 8, 2, 4, 4, 3, 5, 3],
    ];
    {
        let answers: Vec<bool> = examples.iter().map(|a| Solution::can_sort(a.clone())).collect();
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
        let answers: Vec<bool> = cases.iter().map(|a| Solution::can_sort(a.clone())).collect();
        let inp = build_input_multi(&cases);
        let outp = build_output_multi(&answers);
        if seen.insert(inp.clone()) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }

    let edges: Vec<Vec<i64>> = vec![
        vec![1, 1],
        vec![1, 2],
        vec![2, 1],
        vec![1_000_000_000, 1_000_000_000],
        vec![1, 1_000_000_000],
        vec![1_000_000_000, 1],
        vec![1, 1, 1, 1, 1],
        vec![5, 3, 4, 2, 1],
        vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
        vec![10, 9, 8, 7, 6, 5, 4, 3, 2, 1],
    ];
    for chunk in edges.chunks(3) {
        if count >= target { break; }
        let cases: Vec<Vec<i64>> = chunk.to_vec();
        let answers: Vec<bool> = cases.iter().map(|a| Solution::can_sort(a.clone())).collect();
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
            let mode = rng.gen_range_usize(0, 9);
            cases.push(build_mode(&mut rng, mode));
        }
        let answers: Vec<bool> = cases.iter().map(|a| Solution::can_sort(a.clone())).collect();
        let inp = build_input_multi(&cases);
        let outp = build_output_multi(&answers);
        if !seen.insert(inp.clone()) { continue; }
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

