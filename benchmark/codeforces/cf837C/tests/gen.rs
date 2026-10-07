use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    x: Vec<i32>,
    y: Vec<i32>,
    a: i32,
    b: i32,
    mutation_kind: u8,
) -> (ret: (usize, i32, i32, Vec<i32>, Vec<i32>))
    requires
        1 <= x.len() <= 100,
        x.len() == y.len(),
        1 <= a && a <= 100,
        1 <= b && b <= 100,
        forall|i: int| 0 <= i && i < x.len() ==> 1 <= #[trigger] x[i] && x[i] <= 100,
        forall|i: int| 0 <= i && i < y.len() ==> 1 <= #[trigger] y[i] && y[i] <= 100,
    ensures
        ret.0 == ret.3.len(),
        ret.0 == ret.4.len(),
        1 <= ret.0 && ret.0 <= 100,
        1 <= ret.1 && ret.1 <= 100,
        1 <= ret.2 && ret.2 <= 100,
        forall|i: int| 0 <= i && i < ret.0 ==> 1 <= #[trigger] ret.3@[i] && ret.3@[i] <= 100,
        forall|i: int| 0 <= i && i < ret.0 ==> 1 <= #[trigger] ret.4@[i] && ret.4@[i] <= 100,
{
    let n = x.len();
    if mutation_kind == 0 {
        // Identity
        (n, a, b, x, y)
    } else if mutation_kind == 1 {
        // Set first x element to 1 (min boundary)
        let mut mx = x;
        mx.set(0, 1);
        (n, a, b, mx, y)
    } else if mutation_kind == 2 {
        // Set first y element to 100 (max boundary)
        let mut my = y;
        my.set(0, 100);
        (n, a, b, x, my)
    } else if mutation_kind == 3 {
        // Set first x element to 100 (max boundary)
        let mut mx = x;
        mx.set(0, 100);
        (n, a, b, mx, y)
    } else if mutation_kind == 4 {
        // Set first y element to 1 (min boundary)
        let mut my = y;
        my.set(0, 1);
        (n, a, b, x, my)
    } else if mutation_kind == 5 && n < 100 {
        // Grow arrays by pushing an element
        let mut mx = x;
        let mut my = y;
        mx.push(1);
        my.push(1);
        (n + 1, a, b, mx, my)
    } else if mutation_kind == 6 && n > 1 {
        // Shrink arrays by popping
        let mut mx = x;
        let mut my = y;
        mx.pop();
        my.pop();
        (n - 1, a, b, mx, my)
    } else if mutation_kind == 7 {
        // Swap a and b
        (n, b, a, x, y)
    } else if mutation_kind == 8 {
        // Set a to 100 (large paper)
        (n, 100, b, x, y)
    } else if mutation_kind == 9 {
        // Set b to 100 (large paper)
        (n, a, 100, x, y)
    } else if mutation_kind == 10 {
        // Set a and b to 1 (smallest paper)
        (n, 1, 1, x, y)
    } else {
        // Fallback: identity
        (n, a, b, x, y)
    }
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

fn build_input(a: i32, b: i32, seals: &[(i32, i32)]) -> String {
    let mut s = format!("{} {} {}\n", seals.len(), a, b);
    for &(x, y) in seals { s.push_str(&format!("{} {}\n", x, y)); }
    s
}

fn build_output(ans: i32) -> String { format!("{}\n", ans) }

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(837);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |a: i32, b: i32, seals: Vec<(i32, i32)>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if a < 1 || a > 100 || b < 1 || b > 100 { return; }
        if seals.is_empty() || seals.len() > 100 { return; }
        for &(x, y) in &seals { if x < 1 || x > 100 || y < 1 || y > 100 { return; } }
        let key = format!("{} {}|{:?}", a, b, seals);
        if !seen.insert(key) { return; }
        let inp = build_input(a, b, &seals);
        let xs: Vec<i32> = seals.iter().map(|p| p.0).collect();
        let ys: Vec<i32> = seals.iter().map(|p| p.1).collect();
        let ans = Solution::two_seals(seals.len(), a, b, xs, ys);
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Examples
    emit(2, 2, vec![(1, 2), (2, 1)], &mut seen, &mut out, &mut count);
    emit(10, 9, vec![(2, 3), (1, 1), (5, 10), (9, 11)], &mut seen, &mut out, &mut count);
    emit(10, 10, vec![(6, 6), (7, 7), (20, 5)], &mut seen, &mut out, &mut count);

    // Edges
    emit(1, 1, vec![(1, 1)], &mut seen, &mut out, &mut count);
    emit(100, 100, vec![(50, 50), (50, 50)], &mut seen, &mut out, &mut count);
    emit(1, 1, vec![(1, 1), (1, 1)], &mut seen, &mut out, &mut count);

    while count < target {
        let n = rng.gen_range_usize(1, 10);
        let a = rng.gen_range_i32(1, 100);
        let b = rng.gen_range_i32(1, 100);
        let seals: Vec<(i32, i32)> = (0..n).map(|_| (
            rng.gen_range_i32(1, 100),
            rng.gen_range_i32(1, 100),
        )).collect();
        emit(a, b, seals, &mut seen, &mut out, &mut count);
    }
}

