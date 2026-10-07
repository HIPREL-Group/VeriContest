use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (result: (Vec<i32>, usize))
    requires
        1 <= values.len() <= 100,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] as int <= 100,
    ensures
        1 <= result.1 <= 100,
        result.0.len() == result.1,
        forall|i: int| 0 <= i < result.1 as int ==> 1 <= #[trigger] result.0[i] as int <= 100,
{
    let n: usize = values.len();
    let mut a: Vec<i32> = Vec::new();
    let mut pos: usize = 0;

    while pos < n
        invariant
            n == values.len(),
            1 <= n <= 100,
            0 <= pos <= n,
            a.len() == pos,
            forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] as int <= 100,
            forall|k: int| 0 <= k < pos as int ==> a[k] == values[k],
            forall|k: int| 0 <= k < pos as int ==> 1 <= #[trigger] a[k] as int <= 100,
        decreases n - pos,
    {
        a.push(values[pos]);
        pos = pos + 1;
    }

    (a, n)
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

fn build_input(a: &[i32]) -> String {
    let mut s = format!("{}\n", a.len());
    let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(res: &[i32]) -> String {
    let parts: Vec<String> = res.iter().map(|x| x.to_string()).collect();
    let mut s = parts.join(" ");
    s.push('\n');
    s
}

fn build_arr(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    match mode {
        0 => vec![1; n],
        1 => vec![100; n],
        2 => (0..n).map(|i| if i % 2 == 0 { 1 } else { 100 }).collect(),
        3 => (0..n).map(|i| (i as i32 % 100 + 1)).collect(),
        4 => (0..n).map(|i| (n - i) as i32 % 100 + 1).collect(),
        5 => (0..n).map(|_| rng.gen_range_i32(1, 100)).collect(),
        6 => (0..n).map(|_| rng.gen_range_i32(1, 10)).collect(),
        7 => (0..n).map(|_| rng.gen_range_i32(90, 100)).collect(),
        8 => {
            let half = n / 2;
            let mut v = Vec::with_capacity(n);
            for _ in 0..half { v.push(1); }
            for _ in half..n { v.push(100); }
            v
        }
        _ => (0..n).map(|_| rng.gen_range_i32(1, 100)).collect(),
    }
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let modes = 10usize;
    let mut t = 0usize;
    while count < target {
        let mode = t % modes;
        t += 1;
        let n = match mode {
            0 => 1,
            1 => 100,
            2 => 2,
            3 => rng.gen_range_usize(3, 100),
            4 => rng.gen_range_usize(3, 100),
            5 => rng.gen_range_usize(1, 100),
            6 => rng.gen_range_usize(1, 100),
            7 => rng.gen_range_usize(1, 100),
            8 => rng.gen_range_usize(2, 100),
            _ => rng.gen_range_usize(1, 100),
        };
        let a = build_arr(&mut rng, mode, n);
        let key = format!("{:?}", a);
        if !seen.insert(key) { continue; }
        let inp = build_input(&a);
        let r = Solution::gravity_flip(a.clone(), n);
        let outs = build_output(&r);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
        if t > 100000 { break; }
    }
}

