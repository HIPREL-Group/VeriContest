use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    bits: &Vec<i32>,
) -> (result: (usize, Vec<i32>))
    requires
        1 <= n <= 100,
        bits.len() == n,
        forall|i: int| 0 <= i < n ==> (#[trigger] (bits[i] as int) == 0 || (bits[i] as int) == 1),
    ensures
        1 <= result.0 <= 100,
        result.1.len() == result.0,
        forall|i: int| 0 <= i < result.0 ==> (#[trigger] (result.1[i] as int) == 0 || (result.1[i] as int) == 1),
{
    let mut a: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            a.len() == i,
            bits.len() == n,
            1 <= n <= 100,
            forall|k: int| 0 <= k < i as int ==> (#[trigger] (a[k] as int) == 0 || (a[k] as int) == 1),
            forall|k: int| 0 <= k < n ==> (#[trigger] (bits[k] as int) == 0 || (bits[k] as int) == 1),
        decreases n - i,
    {
        let v = bits[i];
        a.push(v);
        i = i + 1;
    }
    (n, a)
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

fn build_input(a: &[i32]) -> String {
    let mut s = format!("{}\n", a.len());
    let parts: Vec<String> = a.iter().map(|v| v.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(ans: i128) -> String { format!("{}\n", ans) }

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(61701);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |a: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if a.is_empty() || a.len() > 100 { return; }
        for &v in &a { if v != 0 && v != 1 { return; } }
        let key = format!("{:?}", a);
        if !seen.insert(key) { return; }
        let inp = build_input(&a);
        let ans = Solution::chocolate_ways(a.len(), a.clone());
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // All zeros / all ones for various n
    for n in 1..=100usize {
        emit(vec![0; n], &mut seen, &mut out, &mut count);
        if count >= target { break; }
    }
    for n in 1..=20usize {
        emit(vec![1; n], &mut seen, &mut out, &mut count);
    }

    // Two ones at extremes
    for n in 2..=100usize {
        let mut v = vec![0; n]; v[0] = 1; v[n - 1] = 1;
        emit(v, &mut seen, &mut out, &mut count);
        if count >= target { break; }
    }

    // Three ones spaced
    for n in 5..=100usize {
        let mut v = vec![0; n]; v[0] = 1; v[n / 2] = 1; v[n - 1] = 1;
        emit(v, &mut seen, &mut out, &mut count);
        if count >= target { break; }
    }

    // Alternating
    for n in [2usize, 4, 6, 10, 50, 100] {
        let v: Vec<i32> = (0..n).map(|i| (i % 2) as i32).collect();
        emit(v, &mut seen, &mut out, &mut count);
        let v2: Vec<i32> = (0..n).map(|i| ((i + 1) % 2) as i32).collect();
        emit(v2, &mut seen, &mut out, &mut count);
    }

    while count < target {
        let n = rng.gen_range_usize(1, 100);
        let p = match rng.gen_range_usize(0, 5) {
            0 => 1,
            1 => 2,
            2 => 5,
            3 => 8,
            _ => 4,
        };
        let a: Vec<i32> = (0..n).map(|_| if rng.gen_range_usize(0, 9) < p { 1 } else { 0 }).collect();
        emit(a, &mut seen, &mut out, &mut count);
    }
}

