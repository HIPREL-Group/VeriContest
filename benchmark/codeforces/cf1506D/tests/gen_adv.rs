use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
) -> (a: Vec<i32>)
    requires
        1 <= values.len() <= 200000,
        forall|j: int| 0 <= j < values.len() ==> 1 <= #[trigger] values[j] <= values.len(),
    ensures
        1 <= a.len() <= 200000,
        a.len() == values.len(),
        forall|j: int| 0 <= j < a.len() as int ==> 1 <= #[trigger] a[j] <= a.len(),
{
    let n = values.len();
    let mut a: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            1 <= n <= 200000,
            0 <= i <= n,
            a.len() == i,
            forall|j: int| 0 <= j < values.len() ==> 1 <= #[trigger] values[j] <= values.len(),
            forall|k: int| 0 <= k < i as int ==> #[trigger] a[k] == values[k],
        decreases n - i,
    {
        a.push(values[i]);
        i += 1;
    }
    assert(forall|k: int| 0 <= k < a.len() as int ==> #[trigger] a[k] == values[k]);
    a
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

fn build_output(answers: &[i32]) -> String {
    let mut s = String::new();
    for &a in answers {
        s.push_str(&format!("{}\n", a));
    }
    s
}

fn gen_arr(rng: &mut Rng, n: usize, mode: u64) -> Vec<i32> {
    let mut a: Vec<i32> = Vec::with_capacity(n);
    let nm = (n as i32).max(1);
    match mode {
        0 => for _ in 0..n { a.push(1); },
        1 => for _ in 0..n { a.push(nm); },
        2 => for i in 0..n { a.push((i % n).max(0) as i32 + 1); },
        3 => { // half 1s, half 2s if n >= 2
            for i in 0..n {
                let v: i32 = if n >= 2 { if i < n / 2 { 1 } else { 2 } } else { 1 };
                a.push(v);
            }
        }
        4 => { // dominated by 1
            for _ in 0..n {
                if nm >= 2 && rng.next_u64() % 4 == 0 {
                    a.push(rng.gen_range_i32(2, nm));
                } else {
                    a.push(1);
                }
            }
        }
        _ => for _ in 0..n { a.push(rng.gen_range_i32(1, nm)); },
    }
    a
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(31337);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // Big case
    {
        let cases: Vec<Vec<i32>> = vec![(1..=2000).collect()];
        let answers: Vec<i32> = cases.iter().map(|a| Solution::min_remaining_after_epic_transformation(a.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    while count < target {
        let t: usize = match count % 5 {
            0 => 1,
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(10, 50),
            3 => rng.gen_range_usize(50, 200),
            _ => rng.gen_range_usize(200, 1000),
        };
        let mut cases: Vec<Vec<i32>> = Vec::new();
        let mut total = 0;
        for _ in 0..t {
            let n = match rng.next_u64() % 5 {
                0 => 1,
                1 => rng.gen_range_usize(1, 5),
                2 => rng.gen_range_usize(5, 30),
                3 => rng.gen_range_usize(30, 100),
                _ => rng.gen_range_usize(100, 500),
            };
            if total + n > 50000 { break; }
            total += n;
            let mode = rng.next_u64() % 6;
            cases.push(gen_arr(&mut rng, n, mode));
        }
        if cases.is_empty() { continue; }
        let answers: Vec<i32> = cases.iter().map(|a| Solution::min_remaining_after_epic_transformation(a.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

