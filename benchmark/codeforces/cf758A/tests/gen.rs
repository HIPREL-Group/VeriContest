use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    base_val: i32,
    step: i32,
    mutation_kind: u8,
) -> (result: (usize, Vec<i32>))
    requires
        1 <= n <= 100,
        0 <= base_val <= 1_000_000,
        0 <= step <= 1_000_000,
    ensures
        1 <= result.0 <= 100,
        result.0 == result.1.len(),
        forall|k: int|
            0 <= k < result.0 as int ==> 0 <= #[trigger] result.1[k] <= 1_000_000,
{
    if mutation_kind == 1 {
        // All same value
        let mut a: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                1 <= n <= 100,
                0 <= base_val <= 1_000_000,
                a.len() == i,
                forall|j: int| 0 <= j < i as int ==> #[trigger] a@[j] == base_val,
            decreases n - i,
        {
            a.push(base_val);
            i += 1;
        }
        proof {
            assert forall|j: int| 0 <= j < a@.len() implies 0 <= #[trigger] a@[j] <= 1_000_000 by {
                assert(a@[j] == base_val);
            };
        }
        return (n, a);
    }

    if mutation_kind == 2 {
        // All zeros
        let mut a: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                1 <= n <= 100,
                a.len() == i,
                forall|j: int| 0 <= j < i as int ==> #[trigger] a@[j] == 0i32,
            decreases n - i,
        {
            a.push(0i32);
            i += 1;
        }
        proof {
            assert forall|j: int| 0 <= j < a@.len() implies 0 <= #[trigger] a@[j] <= 1_000_000 by {
                assert(a@[j] == 0i32);
            };
        }
        return (n, a);
    }

    if mutation_kind == 3 {
        // All max value
        let mut a: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                1 <= n <= 100,
                a.len() == i,
                forall|j: int| 0 <= j < i as int ==> #[trigger] a@[j] == 1_000_000i32,
            decreases n - i,
        {
            a.push(1_000_000i32);
            i += 1;
        }
        proof {
            assert forall|j: int| 0 <= j < a@.len() implies 0 <= #[trigger] a@[j] <= 1_000_000 by {
                assert(a@[j] == 1_000_000i32);
            };
        }
        return (n, a);
    }

    if mutation_kind == 4 {
        // Ascending: base_val, base_val+step, base_val+2*step, ... clamped to 1_000_000
        let mut a: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        let mut cur: i32 = base_val;
        while i < n
            invariant
                0 <= i <= n,
                1 <= n <= 100,
                0 <= base_val <= 1_000_000,
                0 <= step <= 1_000_000,
                0 <= cur <= 1_000_000,
                a.len() == i,
                forall|j: int| 0 <= j < i as int ==> 0 <= #[trigger] a@[j] <= 1_000_000,
            decreases n - i,
        {
            a.push(cur);
            if cur <= 1_000_000 - step {
                cur = cur + step;
            }
            i += 1;
        }
        return (n, a);
    }

    // Default (mutation_kind == 0 or fallback): descending from base_val by step, clamped to 0
    let mut a: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    let mut cur: i32 = base_val;
    while i < n
        invariant
            0 <= i <= n,
            1 <= n <= 100,
            0 <= base_val <= 1_000_000,
            0 <= step <= 1_000_000,
            0 <= cur <= 1_000_000,
            a.len() == i,
            forall|j: int| 0 <= j < i as int ==> 0 <= #[trigger] a@[j] <= 1_000_000,
        decreases n - i,
    {
        a.push(cur);
        if cur >= step {
            cur = cur - step;
        }
        i += 1;
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

fn build_input(a: &[i32]) -> String {
    let mut s = format!("{}\n", a.len());
    let parts: Vec<String> = a.iter().map(|v| v.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(ans: i32) -> String { format!("{}\n", ans) }

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(758);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |a: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if a.is_empty() || a.len() > 100 { return; }
        for &v in &a { if v < 0 || v > 1_000_000 { return; } }
        let key = format!("{:?}", a);
        if !seen.insert(key) { return; }
        let inp = build_input(&a);
        let ans = Solution::holiday_equality_burles(a.len(), a.clone());
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Examples
    emit(vec![0, 1, 2, 3, 4], &mut seen, &mut out, &mut count);
    emit(vec![1, 1, 0, 1, 1], &mut seen, &mut out, &mut count);
    emit(vec![1, 3, 1], &mut seen, &mut out, &mut count);
    emit(vec![12], &mut seen, &mut out, &mut count);

    // Edges
    emit(vec![0], &mut seen, &mut out, &mut count);
    emit(vec![1_000_000], &mut seen, &mut out, &mut count);
    emit(vec![0; 100], &mut seen, &mut out, &mut count);
    emit(vec![1_000_000; 100], &mut seen, &mut out, &mut count);
    emit(vec![0, 1_000_000], &mut seen, &mut out, &mut count);

    while count < target {
        let n = rng.gen_range_usize(1, 100);
        let max_v: i32 = match rng.gen_range_usize(0, 4) {
            0 => 5,
            1 => 100,
            2 => 10_000,
            _ => 1_000_000,
        };
        let a: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(0, max_v)).collect();
        emit(a, &mut seen, &mut out, &mut count);
    }
}

