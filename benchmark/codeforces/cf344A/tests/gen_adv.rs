use vstd::prelude::*;

verus! {

pub fn generate_test_case(bits: &Vec<u8>) -> (res: Vec<u8>)
    requires
        1 <= bits.len() <= 100000,
        forall|i: int| 0 <= i < bits.len() ==> (#[trigger] bits[i] as int == 0 || bits[i] as int == 1),
    ensures
        1 <= res.len() <= 100000,
        res.len() == bits.len(),
        forall|i: int| 0 <= i < res.len() ==> (#[trigger] res[i] as int == 0 || res[i] as int == 1),
{
    let n = bits.len();
    let mut res: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == bits.len(),
            0 <= i <= n,
            res.len() == i,
            forall|k: int| 0 <= k < bits.len() ==> (#[trigger] bits[k] as int == 0 || bits[k] as int == 1),
            forall|k: int| 0 <= k < i as int ==> (#[trigger] res[k] as int == 0 || res[k] as int == 1),
            forall|k: int| 0 <= k < i as int ==> res[k] == bits[k],
        decreases n - i,
    {
        res.push(bits[i]);
        i = i + 1;
    }
    res
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
    fn gen_bit(&mut self) -> u8 { (self.next_u64() & 1) as u8 }
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

fn make_bits(rng: &mut Rng, mode: usize, n: usize) -> Vec<u8> {
    let mut bits: Vec<u8> = Vec::with_capacity(n);
    match mode {
        0 => for _ in 0..n { bits.push(0); },
        1 => for _ in 0..n { bits.push(1); },
        2 => for i in 0..n { bits.push((i & 1) as u8); },
        3 => for i in 0..n { bits.push(((i + 1) & 1) as u8); },
        4 => for i in 0..n { bits.push(((i / 2) & 1) as u8); },
        5 => {
            let mut cur: u8 = rng.gen_bit();
            let mut remaining = n;
            while remaining > 0 {
                let len = rng.gen_range_usize(1, remaining.min(10));
                for _ in 0..len { bits.push(cur); }
                cur = 1 - cur;
                remaining -= len;
            }
        }
        6 => {
            let half = n / 2;
            for _ in 0..half { bits.push(0); }
            for _ in half..n { bits.push(1); }
        }
        7 => for _ in 0..n {
            if rng.gen_range_usize(0, 9) == 0 { bits.push(1); } else { bits.push(0); }
        },
        8 => for _ in 0..n { bits.push(rng.gen_bit()); },
        9 => {
            let mid = n / 2;
            for i in 0..n { bits.push(if i < mid { 0 } else { 1 }); }
        }
        _ => for _ in 0..n { bits.push(rng.gen_bit()); },
    }
    bits.truncate(n);
    while bits.len() < n { bits.push(0); }
    bits
}

fn build_input(magnets: &[u8]) -> String {
    let mut s = format!("{}\n", magnets.len());
    for &m in magnets {
        if m == 0 { s.push_str("01\n"); } else { s.push_str("10\n"); }
    }
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
    let modes = 10usize;
    let mut t = 0usize;
    while count < target {
        let mode = t % modes;
        t += 1;
        let n = match mode {
            0 => 1,
            1 => 2,
            2 => 100000,
            3 => 1 + (t % 20),
            4 => 50,
            5 => 1000,
            6 => 100,
            7 => 500 + (t % 100),
            8 => 10000,
            9 => 99999,
            _ => 1 + rng.gen_range_usize(0, 500),
        };
        let n = n.max(1).min(100000);
        let bits = make_bits(&mut rng, mode, n);
        let key = format!("{:?}", bits);
        if !seen.insert(key) { continue; }
        let inp = build_input(&bits);
        let ans = Solution::count_magnet_groups(bits.clone());
        let outs = format!("{}\n", ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
        if t > 100000 { break; }
    }
}

