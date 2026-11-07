use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    bits: &Vec<i32>,
    zero_idx: usize,
) -> (a: Vec<i32>)
    requires
        1 <= bits.len() <= 200_000,
        zero_idx < bits.len(),
        forall|i: int| 0 <= i < bits.len() ==> (#[trigger] bits[i] == 0 || bits[i] == 1),
    ensures
        1 <= a.len() <= 200_000,
        a.len() == bits.len(),
        forall|i: int| 0 <= i < a.len() ==> (#[trigger] a[i] == 0 || a[i] == 1),
        exists|i: int| 0 <= i < a.len() && #[trigger] a[i] == 0,
{
    let n = bits.len();
    let mut a: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == bits.len(),
            zero_idx < n,
            0 <= i <= n,
            a.len() == i,
            forall|k: int| 0 <= k < bits.len() ==> (#[trigger] bits[k] == 0 || bits[k] == 1),
            forall|k: int| 0 <= k < i as int && k != zero_idx as int ==> #[trigger] a[k] == bits[k],
            forall|k: int| 0 <= k < i as int && k == zero_idx as int ==> #[trigger] a[k] == 0,
            forall|k: int| 0 <= k < i as int ==> (#[trigger] a[k] == 0 || a[k] == 1),
        decreases n - i,
    {
        if i == zero_idx {
            a.push(0);
        } else {
            a.push(bits[i]);
        }
        i = i + 1;
    }

    proof {
        assert(a[zero_idx as int] == 0);
        assert(exists|i: int| 0 <= i < a.len() && #[trigger] a[i] == 0);
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
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let r = (hi as i64 - lo as i64 + 1) as u64;
        (lo as i64 + (self.next_u64() as u64 % r) as i64) as i32
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

fn build_output(ans: i32) -> String { format!("{}\n", ans) }

fn random_array_with_zero(rng: &mut Rng, len: usize, ones_prob_mod: usize) -> Vec<i32> {
    let mut v: Vec<i32> = (0..len).map(|_| {
        let r = rng.gen_range_i32(0, ones_prob_mod as i32 - 1);
        if r > 0 { 1 } else { 0 }
    }).collect();
    if !v.iter().any(|&x| x == 0) {
        v[0] = 0;
    }
    v
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(987654321);
    let mut seen: HashSet<u64> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |a: Vec<i32>, seen: &mut HashSet<u64>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if !a.iter().any(|&x| x == 0) { return; }
        let mut h: u64 = 1469598103934665603;
        h ^= a.len() as u64;
        h = h.wrapping_mul(1099511628211);
        for &x in &a { h ^= x as u64; h = h.wrapping_mul(1099511628211); }
        if !seen.insert(h) { return; }
        let inp = build_input(&a);
        let ans = Solution::maximal_continuous_rest(a);
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Edge patterns
    for &n in &[1usize, 2, 5, 10, 100, 1000, 10_000, 100_000, 200_000] {
        // single 0 at start
        let mut v = vec![1i32; n]; v[0] = 0;
        emit(v, &mut seen, &mut out, &mut count);
        // single 0 at end
        let mut v = vec![1i32; n]; v[n-1] = 0;
        emit(v, &mut seen, &mut out, &mut count);
        // single 0 in middle
        let mut v = vec![1i32; n]; v[n/2] = 0;
        emit(v, &mut seen, &mut out, &mut count);
        // alternating
        let v: Vec<i32> = (0..n).map(|i| if i % 2 == 0 { 0 } else { 1 }).collect();
        emit(v, &mut seen, &mut out, &mut count);
        // all zeros
        emit(vec![0i32; n], &mut seen, &mut out, &mut count);
    }

    let mut tries = 0;
    while count < target && tries < 5000 {
        tries += 1;
        let n = match tries % 6 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(5, 50),
            2 => rng.gen_range_usize(50, 500),
            3 => rng.gen_range_usize(500, 5_000),
            4 => rng.gen_range_usize(5_000, 50_000),
            _ => rng.gen_range_usize(50_000, 200_000),
        };
        let prob_mod = match tries % 4 {
            0 => 2usize,
            1 => 3,
            2 => 5,
            _ => 10,
        };
        let v = random_array_with_zero(&mut rng, n, prob_mod);
        emit(v, &mut seen, &mut out, &mut count);
    }
}

