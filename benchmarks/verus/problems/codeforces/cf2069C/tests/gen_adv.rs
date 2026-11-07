use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (result: Vec<i32>)
    requires
        3 <= values.len() <= 200_000,
        forall|k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 3,
    ensures
        3 <= result.len() <= 200_000,
        forall|k: int| 0 <= k < result.len() ==> 1 <= #[trigger] result[k] <= 3,
{
    let mut out: Vec<i32> = Vec::new();
    let n = values.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            3 <= n <= 200_000,
            i <= n,
            out.len() == i,
            forall|k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 3,
            forall|k: int| 0 <= k < out.len() ==> #[trigger] out[k] == values[k],
            forall|k: int| 0 <= k < out.len() ==> 1 <= #[trigger] out[k] <= 3,
        decreases n - i,
    {
        out.push(values[i]);
        i = i + 1;
    }
    out
}

}

extern crate serde_json;
use serde_json::json;
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
    fn gen_i32_in(&mut self, lo: i32, hi: i32) -> i32 {
        let r = (hi - lo + 1) as u64;
        lo + (self.next_u64() % r) as i32
    }
}

struct Solution;
include!("../code.rs");

// code.rs is O(n^3): outer i, inner j, inner-inner k. Cap n for runtime.
const MAX_N_RUN: usize = 500;

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
        if a.len() < 3 || a.len() > MAX_N_RUN { return; }
        if a.iter().any(|&x| x < 1 || x > 3) { return; }
        let mut h: u64 = 1469598103934665603;
        h ^= a.len() as u64;
        h = h.wrapping_mul(1099511628211);
        for &x in &a {
            h ^= x as u64;
            h = h.wrapping_mul(1099511628211);
        }
        if !seen.insert(h) { return; }
        let result = Solution::count_beautiful_subsequences(a.clone());
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        let inp_str = format!("1\n{}\n{}\n", a.len(), parts.join(" "));
        let out_str = format!("{}\n", result);
        writeln!(out, "{}", json!({"input": inp_str, "output": out_str})).unwrap();
        *count += 1;
    };

    // Edge: all permutations of length 3
    let mut a = 1i32;
    while a <= 3 {
        let mut b = 1i32;
        while b <= 3 {
            let mut c = 1i32;
            while c <= 3 {
                emit(vec![a, b, c], &mut seen, &mut out, &mut count);
                c += 1;
            }
            b += 1;
        }
        a += 1;
    }

    // Edge: uniform arrays
    for &n in &[3usize, 4, 5, 10, 50, 100, 200, 500] {
        emit(vec![1i32; n], &mut seen, &mut out, &mut count);
        emit(vec![2i32; n], &mut seen, &mut out, &mut count);
        emit(vec![3i32; n], &mut seen, &mut out, &mut count);
    }

    // Edge: 1,2,3 repeating (many beautiful triplets)
    for &n in &[3usize, 6, 9, 30, 60, 99, 300, 498] {
        let v: Vec<i32> = (0..n).map(|i| ((i % 3) as i32) + 1).collect();
        emit(v, &mut seen, &mut out, &mut count);
    }

    // Edge: blocks — k 1's, k 2's, k 3's
    for &k in &[1usize, 2, 5, 10, 20, 50, 100, 166] {
        let n = 3 * k;
        if n < 3 || n > MAX_N_RUN { continue; }
        let mut v = Vec::with_capacity(n);
        for _ in 0..k { v.push(1); }
        for _ in 0..k { v.push(2); }
        for _ in 0..k { v.push(3); }
        emit(v, &mut seen, &mut out, &mut count);
    }

    // Edge: 1..many 2's..3 (max contribution from 2s)
    for &mid in &[0usize, 1, 5, 50, 100, 200, 498] {
        let n = 2 + mid;
        if n < 3 || n > MAX_N_RUN { continue; }
        let mut v = Vec::with_capacity(n);
        v.push(1);
        for _ in 0..mid { v.push(2); }
        v.push(3);
        emit(v, &mut seen, &mut out, &mut count);
    }

    // Edge: alternating 1,3 (no 2s)
    for &n in &[3usize, 4, 10, 100, 500] {
        let v: Vec<i32> = (0..n).map(|i| if i % 2 == 0 { 1 } else { 3 }).collect();
        emit(v, &mut seen, &mut out, &mut count);
    }

    // Edge: descending pattern (no 1<2<3 in order)
    for &n in &[3usize, 10, 100, 500] {
        let mut v = Vec::with_capacity(n);
        for i in 0..n {
            v.push(((n - 1 - i) % 3) as i32 + 1);
        }
        emit(v, &mut seen, &mut out, &mut count);
    }

    // Edge: prefix of 1's, then 3, then 2's, then 3
    for &k in &[1usize, 5, 20, 100, 248] {
        let n = k * 2 + 2;
        if n < 3 || n > MAX_N_RUN { continue; }
        let mut v = Vec::with_capacity(n);
        for _ in 0..k { v.push(1); }
        v.push(3);
        for _ in 0..k { v.push(2); }
        v.push(3);
        emit(v, &mut seen, &mut out, &mut count);
    }

    // Edge: 1's followed by 3's (no 2s)
    for &k in &[1usize, 2, 5, 50, 250] {
        let n = 2 * k;
        if n < 3 || n > MAX_N_RUN { continue; }
        let mut v = Vec::with_capacity(n);
        for _ in 0..k { v.push(1); }
        for _ in 0..k { v.push(3); }
        emit(v, &mut seen, &mut out, &mut count);
    }

    // Random arrays at various scales
    let mut tries = 0;
    while count < target && tries < 5000 {
        tries += 1;
        let n = match tries % 5 {
            0 => rng.gen_range_usize(3, 5),
            1 => rng.gen_range_usize(5, 30),
            2 => rng.gen_range_usize(30, 100),
            3 => rng.gen_range_usize(100, 250),
            _ => rng.gen_range_usize(250, MAX_N_RUN),
        };
        let v: Vec<i32> = (0..n).map(|_| rng.gen_i32_in(1, 3)).collect();
        emit(v, &mut seen, &mut out, &mut count);
    }

    eprintln!("Generated {} adversarial test cases", count);
}
