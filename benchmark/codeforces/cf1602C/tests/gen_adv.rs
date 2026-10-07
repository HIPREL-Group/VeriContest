use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, raw_cnt: &Vec<i32>) -> (result: (usize, Vec<i32>))
    requires
        1 <= n <= 200_000,
        raw_cnt.len() == 30,
        forall|i: int| 0 <= i < 30 ==> 0 <= #[trigger] raw_cnt[i] <= n,
    ensures
        1 <= result.0 <= 200_000,
        result.0 == n,
        result.1.len() == 30,
        forall|i: int| 0 <= i < 30 ==> 0 <= #[trigger] result.1[i] <= result.0,
{
    let mut cnt: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < 30
        invariant
            i <= 30,
            cnt.len() == i,
            raw_cnt.len() == 30,
            forall|k: int| 0 <= k < 30 ==> 0 <= #[trigger] raw_cnt[k] <= n,
            forall|k: int| 0 <= k < i as int ==> 0 <= #[trigger] cnt[k] <= n,
            forall|k: int| 0 <= k < i as int ==> cnt[k] == raw_cnt[k],
        decreases 30 - i,
    {
        cnt.push(raw_cnt[i]);
        i = i + 1;
    }
    (n, cnt)
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
        let x = self.next_u64();
        let v = ((x >> 32) ^ x) as u128;
        (lo as i128 + (v % r) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let x = self.next_u64();
        let v = ((x >> 32) ^ x) as usize;
        lo + v % (hi - lo + 1)
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

fn count_bits(a: &[i32]) -> Vec<i32> {
    let mut cnt = vec![0i32; 30];
    for &x in a {
        for b in 0..30 {
            if ((x >> b) & 1) == 1 { cnt[b] += 1; }
        }
    }
    cnt
}

fn build_input(cases: &[Vec<i32>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for a in cases {
        s.push_str(&format!("{}\n", a.len()));
        let parts: Vec<String> = a.iter().map(|v| v.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[Vec<i32>]) -> String {
    let mut s = String::new();
    for ks in answers {
        let parts: Vec<String> = ks.iter().map(|v| v.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn make_test(rng: &mut Rng, mode: usize) -> Vec<i32> {
    match mode {
        0 => vec![rng.gen_range_i64(0, (1 << 30) - 1) as i32],
        1 => { let n = rng.gen_range_usize(1, 50); vec![0i32; n] }
        2 => {
            let n = rng.gen_range_usize(1, 50);
            let v = rng.gen_range_i64(0, (1 << 30) - 1) as i32;
            vec![v; n]
        }
        3 => {
            let n = rng.gen_range_usize(1, 50);
            (0..n).map(|_| rng.gen_range_i64(0, 7) as i32).collect()
        }
        4 => {
            let n = rng.gen_range_usize(1, 50);
            (0..n).map(|_| rng.gen_range_i64(0, (1 << 30) - 1) as i32).collect()
        }
        5 => {
            let n = 1000;
            (0..n).map(|_| rng.gen_range_i64(0, (1 << 30) - 1) as i32).collect()
        }
        6 => {
            // single bit set
            let n = rng.gen_range_usize(1, 50);
            (0..n).map(|_| 1i32 << rng.gen_range_usize(0, 29)).collect()
        }
        7 => {
            // power-of-2 sized
            let n = 16;
            (0..n).map(|_| rng.gen_range_i64(0, (1 << 30) - 1) as i32).collect()
        }
        8 => {
            // all max value
            let n = rng.gen_range_usize(1, 50);
            vec![(1 << 30) - 1; n]
        }
        9 => {
            // all 1s
            let n = rng.gen_range_usize(1, 50);
            vec![1i32; n]
        }
        _ => {
            let n = rng.gen_range_usize(1, 100);
            (0..n).map(|_| rng.gen_range_i64(0, (1 << 30) - 1) as i32).collect()
        }
    }
}

fn main() {
    let mut rng = Rng::new(1);
    let modes = 10usize;
    let total = 200usize;

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;
    let mut idx = 0;
    while count < total {
        let t: usize = if count < 10 { 1 } else { rng.gen_range_usize(1, 10) };
        let mut cases: Vec<Vec<i32>> = Vec::new();
        for _ in 0..t {
            let mode = idx % modes;
            idx += 1;
            cases.push(make_test(&mut rng, mode));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<Vec<i32>> = cases.iter().map(|a| {
            let cnt = count_bits(a);
            Solution::valid_k_values(a.len(), cnt)
        }).collect();
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

