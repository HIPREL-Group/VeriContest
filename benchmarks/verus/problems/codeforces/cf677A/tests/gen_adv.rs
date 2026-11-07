use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    h: i32,
    fillers: &Vec<i32>,
) -> (result: (Vec<i32>, usize, i32))
    requires
        1 <= n <= 1000,
        1 <= h <= 1000,
        fillers.len() == n,
        forall|i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 2 * (h as int),
    ensures
        ({
            let a = result.0;
            let nn = result.1;
            let hh = result.2;
            &&& 1 <= nn <= 1000
            &&& a.len() == nn
            &&& 1 <= hh <= 1000
            &&& forall|i: int| 0 <= i < a.len() as int ==> 1 <= #[trigger] a[i] <= 2 * (hh as int)
        }),
{
    let mut a: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            a.len() == i,
            fillers.len() == n,
            1 <= h <= 1000,
            forall|k: int| 0 <= k < i as int ==> 1 <= #[trigger] a[k] <= 2 * (h as int),
            forall|k: int| 0 <= k < fillers.len() ==> 1 <= #[trigger] fillers[k] <= 2 * (h as int),
        decreases n - i,
    {
        a.push(fillers[i]);
        i = i + 1;
    }
    (a, n, h)
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
        lo + (self.next_u64() as i32).rem_euclid(hi - lo + 1)
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

fn build_input(a: &[i32], h: i32) -> String {
    let mut s = format!("{} {}\n", a.len(), h);
    let parts: Vec<String> = a.iter().map(|v| v.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(ans: i32) -> String { format!("{}\n", ans) }

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(67701);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |a: Vec<i32>, h: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if a.is_empty() || a.len() > 1000 || h < 1 || h > 1000 { return; }
        for &v in &a { if v < 1 || v > 2 * h { return; } }
        let key = format!("{}|{:?}", h, a);
        if !seen.insert(key) { return; }
        let inp = build_input(&a, h);
        let ans = Solution::total_road_width(a.clone(), a.len(), h);
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Boundaries
    for &h in &[1i32, 2, 100, 500, 999, 1000] {
        emit(vec![1; 1000], h, &mut seen, &mut out, &mut count);
        emit(vec![2 * h; 1000], h, &mut seen, &mut out, &mut count);
        emit(vec![h; 1000], h, &mut seen, &mut out, &mut count);
        emit(vec![h + 1; 1000], h, &mut seen, &mut out, &mut count);
        emit(vec![1, 2 * h], h, &mut seen, &mut out, &mut count);
    }

    // Various sizes
    for &n in &[1usize, 2, 5, 10, 100, 500, 1000] {
        for &h in &[1i32, 100, 500, 1000] {
            let v: Vec<i32> = (0..n).map(|i| if i % 2 == 0 { 1 } else { 2 * h }).collect();
            emit(v, h, &mut seen, &mut out, &mut count);
        }
    }

    while count < target {
        let n = rng.gen_range_usize(1, 1000);
        let h = rng.gen_range_i32(1, 1000);
        let a: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(1, 2 * h)).collect();
        emit(a, h, &mut seen, &mut out, &mut count);
    }
}

