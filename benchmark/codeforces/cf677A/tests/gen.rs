use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    h: i32,
    fill_val: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, usize, i32))
    requires
        1 <= n <= 1000,
        1 <= h <= 1000,
        1 <= fill_val <= 2 * (h as int),
    ensures
        1 <= result.1 <= 1000,
        result.0.len() == result.1,
        1 <= result.2 <= 1000,
        forall|i: int| 0 <= i < result.0.len() as int ==> 1 <= #[trigger] result.0[i] <= 2 * (result.2 as int),
{
    if mutation_kind == 1 {
        // All elements = 1 (minimum value, all fit under fence)
        let mut a: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                1 <= n <= 1000,
                1 <= h <= 1000,
                a.len() == i,
                forall|j: int| 0 <= j < i as int ==> #[trigger] a@[j] == 1i32,
            decreases n - i,
        {
            a.push(1i32);
            i += 1;
        }
        proof {
            assert forall|j: int| 0 <= j < a@.len() implies 1 <= #[trigger] a@[j] <= 2 * (h as int) by {
                assert(a@[j] == 1i32);
            };
        }
        return (a, n, h);
    }

    if mutation_kind == 2 {
        // All elements = 2*h (maximum value, all must bend)
        let max_val: i32 = 2 * h;
        let mut a: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                1 <= n <= 1000,
                1 <= h <= 1000,
                max_val == 2 * h,
                a.len() == i,
                forall|j: int| 0 <= j < i as int ==> #[trigger] a@[j] == max_val,
            decreases n - i,
        {
            a.push(max_val);
            i += 1;
        }
        proof {
            assert forall|j: int| 0 <= j < a@.len() implies 1 <= #[trigger] a@[j] <= 2 * (h as int) by {
                assert(a@[j] == max_val);
            };
        }
        return (a, n, h);
    }

    if mutation_kind == 3 {
        // All elements = h (boundary: exactly fence height, all fit)
        let mut a: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                1 <= n <= 1000,
                1 <= h <= 1000,
                a.len() == i,
                forall|j: int| 0 <= j < i as int ==> #[trigger] a@[j] == h,
            decreases n - i,
        {
            a.push(h);
            i += 1;
        }
        proof {
            assert forall|j: int| 0 <= j < a@.len() implies 1 <= #[trigger] a@[j] <= 2 * (h as int) by {
                assert(a@[j] == h);
            };
        }
        return (a, n, h);
    }

    if mutation_kind == 4 {
        // All elements = h+1 (just above fence, all must bend)
        let val: i32 = h + 1;
        let mut a: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                1 <= n <= 1000,
                1 <= h <= 1000,
                val == h + 1,
                a.len() == i,
                forall|j: int| 0 <= j < i as int ==> #[trigger] a@[j] == val,
            decreases n - i,
        {
            a.push(val);
            i += 1;
        }
        proof {
            assert forall|j: int| 0 <= j < a@.len() implies 1 <= #[trigger] a@[j] <= 2 * (h as int) by {
                assert(a@[j] == val);
            };
        }
        return (a, n, h);
    }

    // Default (mutation_kind == 0 or fallback): fill with fill_val
    let mut a: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            1 <= n <= 1000,
            1 <= h <= 1000,
            1 <= fill_val <= 2 * (h as int),
            a.len() == i,
            forall|j: int| 0 <= j < i as int ==> #[trigger] a@[j] == fill_val,
        decreases n - i,
    {
        a.push(fill_val);
        i += 1;
    }
    proof {
        assert forall|j: int| 0 <= j < a@.len() implies 1 <= #[trigger] a@[j] <= 2 * (h as int) by {
            assert(a@[j] == fill_val);
        };
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
    let target: usize = 100;
    let mut rng = Rng::new(677);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
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

    // Examples
    emit(vec![4, 5, 14], 7, &mut seen, &mut out, &mut count);
    emit(vec![1, 1, 1, 1, 1, 1], 1, &mut seen, &mut out, &mut count);
    emit(vec![7, 6, 8, 9, 10, 5], 5, &mut seen, &mut out, &mut count);

    // Edges
    emit(vec![1], 1, &mut seen, &mut out, &mut count);
    emit(vec![2], 1, &mut seen, &mut out, &mut count);
    emit(vec![1000], 1000, &mut seen, &mut out, &mut count);
    emit(vec![2000], 1000, &mut seen, &mut out, &mut count);
    emit(vec![1; 1000], 1, &mut seen, &mut out, &mut count);
    emit(vec![2; 1000], 1, &mut seen, &mut out, &mut count);

    while count < target {
        let n = rng.gen_range_usize(1, 200);
        let h = rng.gen_range_i32(1, 1000);
        let a: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(1, 2 * h)).collect();
        emit(a, h, &mut seen, &mut out, &mut count);
    }
}

