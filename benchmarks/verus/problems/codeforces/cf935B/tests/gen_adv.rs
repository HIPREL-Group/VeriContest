use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, moves: &Vec<i32>) -> (result: Vec<i32>)
    requires
        n == moves.len(),
        n > 0,
        n <= 100000,
        forall|j: int| 0 <= j && j < n ==> (moves[j] == 0 || moves[j] == 1),
    ensures
        result.len() == n,
        n == result.len(),
        n > 0,
        n <= 100000,
        forall|j: int| 0 <= j && j < n ==> (result@[j] == 0 || result@[j] == 1),
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            n == moves.len(),
            forall|j: int| 0 <= j && j < n ==> (moves[j] == 0 || moves[j] == 1),
            forall|j: int| 0 <= j && j < i as int ==> (result@[j] == 0 || result@[j] == 1),
            forall|j: int| 0 <= j && j < i as int ==> result@[j] == moves[j],
        decreases n - i,
    {
        result.push(moves[i]);
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

fn build_input(s: &str) -> String { format!("{}\n{}\n", s.len(), s) }
fn build_output(ans: i32) -> String { format!("{}\n", ans) }

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(93501);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |s: String, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if s.is_empty() || s.len() > 100_000 { return; }
        for c in s.chars() { if c != 'U' && c != 'R' { return; } }
        if !seen.insert(s.clone()) { return; }
        let inp = build_input(&s);
        let moves: Vec<i32> = s.chars().map(|c| if c == 'R' { 1 } else { 0 }).collect();
        let ans = Solution::fafa_and_gates(s.len(), moves);
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Boundary
    emit("U".into(), &mut seen, &mut out, &mut count);
    emit("R".into(), &mut seen, &mut out, &mut count);
    emit("U".repeat(100_000), &mut seen, &mut out, &mut count);
    emit("R".repeat(100_000), &mut seen, &mut out, &mut count);
    emit("UR".repeat(50_000), &mut seen, &mut out, &mut count);
    emit("RU".repeat(50_000), &mut seen, &mut out, &mut count);
    emit("UUR".repeat(33_333), &mut seen, &mut out, &mut count);
    emit("URR".repeat(33_333), &mut seen, &mut out, &mut count);
    emit("UURR".repeat(25_000), &mut seen, &mut out, &mut count);
    emit("RRUU".repeat(25_000), &mut seen, &mut out, &mut count);

    // Various sizes
    for &n in &[1usize, 2, 3, 100, 1000, 10_000, 100_000] {
        emit("U".repeat(n), &mut seen, &mut out, &mut count);
        emit("R".repeat(n), &mut seen, &mut out, &mut count);
        let alt: String = (0..n).map(|i| if i % 2 == 0 { 'U' } else { 'R' }).collect();
        emit(alt, &mut seen, &mut out, &mut count);
    }

    while count < target {
        let n = match rng.gen_range_usize(0, 5) {
            0 => 1,
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(10, 100),
            3 => rng.gen_range_usize(100, 1000),
            _ => rng.gen_range_usize(1000, 100_000),
        };
        let p = match rng.gen_range_usize(0, 5) {
            0 => 1,
            1 => 3,
            2 => 5,
            3 => 7,
            _ => 9,
        };
        let s: String = (0..n).map(|_| if rng.gen_range_usize(0, 9) < p { 'R' } else { 'U' }).collect();
        emit(s, &mut seen, &mut out, &mut count);
    }
}

