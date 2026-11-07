use vstd::prelude::*;

verus! {

pub fn generate_test_case(a: Vec<i64>, mutation_kind: u8) -> (result: Vec<i64>)
    requires
        1 <= a.len() <= 100_000,
        forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 1_000_000_000,
    ensures
        1 <= result.len() <= 100_000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        a
    } else if mutation_kind == 1 {
        // set last element to 1 (boundary low)
        let mut p = a;
        let last = p.len() - 1;
        p.set(last, 1);
        p
    } else if mutation_kind == 2 {
        // set last element to 1_000_000_000 (boundary high)
        let mut p = a;
        let last = p.len() - 1;
        p.set(last, 1_000_000_000);
        p
    } else if mutation_kind == 3 {
        // set first element to 1
        let mut p = a;
        p.set(0, 1);
        p
    } else if mutation_kind == 4 {
        // set first element to 1_000_000_000
        let mut p = a;
        p.set(0, 1_000_000_000);
        p
    } else if mutation_kind == 5 && a.len() < 100_000 {
        // grow by one element (push 1)
        let mut p = a;
        p.push(1);
        p
    } else if mutation_kind == 6 && a.len() > 1 {
        // shrink by one element (pop)
        let mut p = a;
        p.pop();
        p
    } else if mutation_kind == 7 {
        // nudge last element up (if < 1_000_000_000)
        let mut p = a;
        let last = p.len() - 1;
        if p[last] < 1_000_000_000 {
            p.set(last, p[last] + 1);
        }
        p
    } else if mutation_kind == 8 {
        // nudge last element down (if > 1)
        let mut p = a;
        let last = p.len() - 1;
        if p[last] > 1 {
            p.set(last, p[last] - 1);
        }
        p
    } else if mutation_kind == 9 {
        // set all elements to 1 (all equal, non-decreasing run = full length)
        let mut p = a;
        let mut i: usize = 0;
        while i < p.len()
            invariant
                0 <= i <= p.len(),
                p.len() == a.len(),
                1 <= p.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> p[j] == 1i64,
                forall|j: int| i <= j < p.len() as int ==> p[j] == a[j],
            decreases p.len() - i,
        {
            p.set(i, 1);
            i += 1;
        }
        p
    } else if mutation_kind == 10 {
        // set all elements to 1_000_000_000 (all equal)
        let mut p = a;
        let mut i: usize = 0;
        while i < p.len()
            invariant
                0 <= i <= p.len(),
                p.len() == a.len(),
                1 <= p.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> p[j] == 1_000_000_000i64,
                forall|j: int| i <= j < p.len() as int ==> p[j] == a[j],
            decreases p.len() - i,
        {
            p.set(i, 1_000_000_000);
            i += 1;
        }
        p
    } else if mutation_kind == 11 {
        // swap first and last elements
        let mut p = a;
        if p.len() > 1 {
            let first = p[0];
            let last_idx = p.len() - 1;
            let last = p[last_idx];
            p.set(0, last);
            p.set(last_idx, first);
        }
        p
    } else {
        // fallback: identity
        a
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

fn build_input(a: &[i64]) -> String {
    let mut s = format!("{}\n", a.len());
    let parts: Vec<String> = a.iter().map(|v| v.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(ans: usize) -> String { format!("{}\n", ans) }

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(580);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |a: Vec<i64>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| -> bool {
        if *count >= target { return false; }
        if a.is_empty() || a.len() > 100_000 { return false; }
        for &v in &a { if v < 1 || v > 1_000_000_000 { return false; } }
        let key = format!("{:?}", a);
        if !seen.insert(key) { return false; }
        let inp = build_input(&a);
        let ans = Solution::longest_non_decreasing_run(a.clone());
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
        true
    };

    // Examples
    emit(vec![2, 2, 1, 3, 4, 1], &mut seen, &mut out, &mut count);
    emit(vec![2, 2, 9], &mut seen, &mut out, &mut count);

    // Edge: single element
    emit(vec![1], &mut seen, &mut out, &mut count);
    emit(vec![1_000_000_000], &mut seen, &mut out, &mut count);

    // Strictly increasing / non-decreasing
    emit(vec![1, 2, 3, 4, 5], &mut seen, &mut out, &mut count);
    emit(vec![5, 5, 5, 5, 5], &mut seen, &mut out, &mut count);
    emit(vec![1, 2, 3, 3, 4, 4, 5], &mut seen, &mut out, &mut count);

    // Strictly decreasing
    emit(vec![5, 4, 3, 2, 1], &mut seen, &mut out, &mut count);
    emit(vec![10, 9, 8, 7, 6, 5], &mut seen, &mut out, &mut count);

    // Mixed patterns
    emit(vec![1, 2, 1, 2, 1, 2], &mut seen, &mut out, &mut count);
    emit(vec![1, 2, 3, 4, 1, 2], &mut seen, &mut out, &mut count);
    emit(vec![3, 2, 1, 1, 2, 3], &mut seen, &mut out, &mut count);

    while count < target {
        let n = rng.gen_range_usize(1, 200);
        let max_v: i64 = match rng.gen_range_usize(0, 4) {
            0 => 2,
            1 => 5,
            2 => 100,
            3 => 1000,
            _ => 1_000_000_000,
        };
        let a: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, max_v)).collect();
        emit(a, &mut seen, &mut out, &mut count);
    }
}

