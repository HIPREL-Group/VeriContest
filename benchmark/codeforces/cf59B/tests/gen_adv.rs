use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    petals: &Vec<i32>,
) -> (result: Vec<i32>)
    requires
        1 <= petals.len() <= 100,
        forall|i: int| 0 <= i < petals.len() ==> 1 <= #[trigger] petals[i] <= 100,
    ensures
        1 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100,
{
    let n = petals.len();
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == petals.len(),
            0 <= i <= n,
            result.len() == i,
            forall|k: int| 0 <= k < petals.len() ==> 1 <= #[trigger] petals[k] <= 100,
            forall|k: int| 0 <= k < i as int ==> 1 <= #[trigger] result[k] <= 100,
            forall|k: int| 0 <= k < i as int ==> result[k] == petals[k],
        decreases n - i,
    {
        result.push(petals[i]);
        i = i + 1;
    }
    result
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
        (lo as i128 + (self.next_u64() as u128 % r) as i128) as i64
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

fn build_output(ans: i32) -> String { format!("{}\n", ans) }

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(5901);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |a: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if a.is_empty() || a.len() > 100 { return; }
        for &v in &a { if v < 1 || v > 100 { return; } }
        let key = format!("{:?}", a);
        if !seen.insert(key) { return; }
        let inp = build_input(&a);
        let ans = Solution::max_loving_petals(a.clone());
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Boundary cases
    for v in 1..=100i32 {
        emit(vec![v], &mut seen, &mut out, &mut count);
        if count >= target { break; }
    }

    // All same
    for v in [1i32, 2, 3, 4, 50, 99, 100] {
        emit(vec![v; 100], &mut seen, &mut out, &mut count);
        emit(vec![v; 50], &mut seen, &mut out, &mut count);
        emit(vec![v; 2], &mut seen, &mut out, &mut count);
    }

    // All evens
    let evens: Vec<i32> = (1..=50).map(|i| 2 * i).collect();
    emit(evens.clone(), &mut seen, &mut out, &mut count);
    // All odds
    let odds: Vec<i32> = (0..50).map(|i| 2 * i + 1).collect();
    emit(odds.clone(), &mut seen, &mut out, &mut count);
    // Mixed
    let mixed: Vec<i32> = (1..=100).collect();
    emit(mixed, &mut seen, &mut out, &mut count);

    while count < target {
        let n = rng.gen_range_usize(1, 100);
        let max_v = match rng.gen_range_usize(0, 4) {
            0 => 2,
            1 => 5,
            2 => 20,
            _ => 100,
        };
        let a: Vec<i32> = (0..n).map(|_| rng.gen_range_i64(1, max_v) as i32).collect();
        emit(a, &mut seen, &mut out, &mut count);
    }
}

