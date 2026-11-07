use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
) -> (a: Vec<i32>)
    requires
        1 <= values.len() <= 50,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100,
    ensures
        1 <= a.len() <= 50,
        forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] as int <= 100,
{
    let n = values.len();
    let mut a: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            a.len() == i,
            forall|k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 100,
            forall|k: int| 0 <= k < i as int ==> #[trigger] a[k] == values[k],
        decreases n - i,
    {
        a.push(values[i]);
        i = i + 1;
    }
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

fn build_output(answers: &[bool]) -> String {
    let mut s = String::new();
    for &a in answers {
        s.push_str(if a { "YES\n" } else { "NO\n" });
    }
    s
}

fn gen_arr(rng: &mut Rng, n: usize, mode: u64) -> Vec<i32> {
    let mut a: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => for _ in 0..n { a.push(1); }, // all 1s
        1 => for _ in 0..n { a.push(100); }, // all 100s
        2 => for i in 0..n { a.push((i % 100 + 1) as i32); }, // 1..100 cycle
        3 => { // 1, 2, ..., n
            for i in 0..n { a.push(((i % 100) + 1) as i32); }
        }
        4 => { // gap of 2 somewhere
            for i in 0..n {
                a.push(if i < n / 2 { 1 } else { 5 });
            }
        }
        5 => { // pair of values close
            let v = rng.gen_range_i32(1, 99);
            for i in 0..n {
                a.push(v + (i as i32 & 1));
            }
        }
        _ => {
            for _ in 0..n { a.push(rng.gen_range_i32(1, 100)); }
        }
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

    // Boundary case: all max sizes
    {
        let cases: Vec<Vec<i32>> = (0..50).map(|_| (1..=50).collect()).collect();
        let answers: Vec<bool> = cases.iter().map(|a| Solution::remove_smallest_possible(a.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    while count < target {
        let t: usize = match count % 5 {
            0 => 1,
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(10, 100),
            3 => rng.gen_range_usize(100, 500),
            _ => rng.gen_range_usize(500, 1000),
        };
        let mut cases: Vec<Vec<i32>> = Vec::new();
        for _ in 0..t {
            let n = match rng.next_u64() % 4 {
                0 => 1,
                1 => rng.gen_range_usize(1, 5),
                2 => rng.gen_range_usize(5, 25),
                _ => rng.gen_range_usize(25, 50),
            };
            let mode = rng.next_u64() % 8;
            cases.push(gen_arr(&mut rng, n, mode));
        }
        let answers: Vec<bool> = cases.iter().map(|a| Solution::remove_smallest_possible(a.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

