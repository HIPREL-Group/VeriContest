use vstd::prelude::*;

verus! {

pub fn generate_test_case(bits: &Vec<u8>) -> (a: Vec<i32>)
    requires
        1 <= bits.len() <= 100,
        forall |k: int| 0 <= k < bits.len() ==> (#[trigger] bits[k] == 0u8 || bits[k] == 1u8),
    ensures
        1 <= a.len() <= 100,
        forall |k: int| 0 <= k < a.len() ==> (#[trigger] a[k] == 0 || a[k] == 1),
{
    let n = bits.len();
    let mut a: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == bits.len(),
            1 <= n <= 100,
            0 <= i <= n,
            a.len() == i,
            forall |k: int| 0 <= k < bits.len() ==> (#[trigger] bits[k] == 0u8 || bits[k] == 1u8),
            forall |k: int| 0 <= k < i as int ==> (#[trigger] a[k] == 0i32 || a[k] == 1i32),
            forall |k: int| 0 <= k < i as int ==> (a[k] == bits[k] as i32),
        decreases n - i,
    {
        let v: i32 = if bits[i] == 1u8 { 1i32 } else { 0i32 };
        a.push(v);
        i = i + 1;
    }
    a
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

fn make_bits_mode(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    match mode {
        0 => for _ in 0..n { v.push(0); },
        1 => for _ in 0..n { v.push(1); },
        2 => for i in 0..n { v.push((i % 2) as i32); },
        3 => for i in 0..n { v.push(((i+1) % 2) as i32); },
        4 => for i in 0..n { v.push(if i < n/2 { 0 } else { 1 }); },
        5 => for i in 0..n { v.push(if i < n/2 { 1 } else { 0 }); },
        6 => for i in 0..n { v.push(if i == 0 || i == n-1 { 1 } else { 0 }); },
        7 => for i in 0..n { v.push(if i == 0 || i == n-1 { 0 } else { 1 }); },
        8 => for _ in 0..n { v.push((rng.next_u64() & 1) as i32); },
        9 => for i in 0..n { v.push(if i % 3 == 0 { 0 } else { 1 }); },
        _ => {
            let k = rng.gen_range_usize(0, n);
            for i in 0..n { v.push(if i < k { 1 } else { 0 }); }
        }
    }
    v
}

fn build_input(bits: &[i32]) -> String {
    let mut s = format!("{}\n", bits.len());
    let parts: Vec<String> = bits.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let modes = 11usize;
    let mut t = 0usize;
    while count < target {
        let mode = t % modes;
        let n = match mode {
            0 => 1 + (t % 5),
            1 => 100,
            2 => 2 + (t % 10),
            3 => if t % 2 == 0 { 1 } else { 100 },
            4 => 10,
            5 => 50,
            6 => 99,
            7 => 3,
            8 => 1 + rng.gen_range_usize(0, 99),
            9 => 17,
            _ => 1 + (t % 100),
        };
        let n = if n < 1 { 1 } else if n > 100 { 100 } else { n };
        let bits = make_bits_mode(&mut rng, mode, n);
        t += 1;
        let key = format!("{:?}", bits);
        if !seen.insert(key) { continue; }
        let inp = build_input(&bits);
        let ans = Solution::max_ones_after_flip(bits.clone());
        let outs = format!("{}\n", ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
        if t > 100000 { break; }
    }
}

