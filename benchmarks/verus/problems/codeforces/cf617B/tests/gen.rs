use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, vals: Vec<i32>, mutation_kind: u8) -> (result: (usize, Vec<i32>))
    requires
        1 <= n <= 100,
        vals.len() == n,
        forall|i: int| 0 <= i < n as int ==> (#[trigger] (vals[i] as int) == 0 || (vals[i] as int) == 1),
    ensures
        1 <= result.0 <= 100,
        result.1.len() == result.0,
        forall|i: int| 0 <= i < result.0 ==> (#[trigger] (result.1[i] as int) == 0 || (result.1[i] as int) == 1),
{
    if mutation_kind == 0 {
        // identity
        (n, vals)
    } else if mutation_kind == 1 {
        // set all elements to 0 (no nuts)
        let mut y = vals;
        let mut i: usize = 0;
        while i < n
            invariant
                1 <= n <= 100,
                y.len() == n,
                0 <= i <= n,
                forall|j: int| 0 <= j < i ==> (#[trigger] y[j] == 0i32),
                forall|j: int| i as int <= j < n as int ==> (#[trigger] (y[j] as int) == 0 || (y[j] as int) == 1),
            decreases n - i,
        {
            y.set(i, 0i32);
            i += 1;
        }
        assert forall|j: int| 0 <= j < y.len() implies (#[trigger] (y[j] as int) == 0 || (y[j] as int) == 1) by {}
        (n, y)
    } else if mutation_kind == 2 {
        // set all elements to 1 (all nuts)
        let mut y = vals;
        let mut i: usize = 0;
        while i < n
            invariant
                1 <= n <= 100,
                y.len() == n,
                0 <= i <= n,
                forall|j: int| 0 <= j < i ==> (#[trigger] y[j] == 1i32),
                forall|j: int| i as int <= j < n as int ==> (#[trigger] (y[j] as int) == 0 || (y[j] as int) == 1),
            decreases n - i,
        {
            y.set(i, 1i32);
            i += 1;
        }
        assert forall|j: int| 0 <= j < y.len() implies (#[trigger] (y[j] as int) == 0 || (y[j] as int) == 1) by {}
        (n, y)
    } else if mutation_kind == 3 && vals.len() >= 1 {
        // flip first element
        let mut y = vals;
        let old = y[0];
        let new_val: i32 = if old == 0 { 1i32 } else { 0i32 };
        y.set(0, new_val);
        assert((new_val as int) == 0 || (new_val as int) == 1);
        assert forall|j: int| 0 <= j < y.len() implies (#[trigger] (y[j] as int) == 0 || (y[j] as int) == 1) by {}
        (n, y)
    } else if mutation_kind == 4 && vals.len() >= 1 {
        // flip last element
        let mut y = vals;
        let last = y.len() - 1;
        let old = y[last];
        let new_val: i32 = if old == 0 { 1i32 } else { 0i32 };
        y.set(last, new_val);
        assert((new_val as int) == 0 || (new_val as int) == 1);
        assert forall|j: int| 0 <= j < y.len() implies (#[trigger] (y[j] as int) == 0 || (y[j] as int) == 1) by {}
        (n, y)
    } else if mutation_kind == 5 {
        // set all to 0, then set first to 1 (exactly one nut)
        let mut y = vals;
        let mut i: usize = 0;
        while i < n
            invariant
                1 <= n <= 100,
                y.len() == n,
                0 <= i <= n,
                forall|j: int| 0 <= j < i ==> (#[trigger] y[j] == 0i32),
                forall|j: int| i as int <= j < n as int ==> (#[trigger] (y[j] as int) == 0 || (y[j] as int) == 1),
            decreases n - i,
        {
            y.set(i, 0i32);
            i += 1;
        }
        y.set(0, 1i32);
        assert forall|j: int| 0 <= j < y.len() implies (#[trigger] (y[j] as int) == 0 || (y[j] as int) == 1) by {}
        (n, y)
    } else {
        // fallback: identity
        (n, vals)
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

fn build_output(ans: i128) -> String { format!("{}\n", ans) }

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(617);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |a: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if a.is_empty() || a.len() > 100 { return; }
        for &v in &a { if v != 0 && v != 1 { return; } }
        let key = format!("{:?}", a);
        if !seen.insert(key) { return; }
        let inp = build_input(&a);
        let ans = Solution::chocolate_ways(a.len(), a.clone());
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Examples
    emit(vec![0, 1, 0], &mut seen, &mut out, &mut count);
    emit(vec![1, 0, 1, 0, 1], &mut seen, &mut out, &mut count);

    // Edges
    emit(vec![0], &mut seen, &mut out, &mut count);
    emit(vec![1], &mut seen, &mut out, &mut count);
    emit(vec![0, 0], &mut seen, &mut out, &mut count);
    emit(vec![1, 1], &mut seen, &mut out, &mut count);
    emit(vec![0; 100], &mut seen, &mut out, &mut count);
    emit(vec![1; 100], &mut seen, &mut out, &mut count);
    emit(vec![1, 0, 1], &mut seen, &mut out, &mut count);
    emit(vec![0, 1, 1, 0], &mut seen, &mut out, &mut count);

    while count < target {
        let n = rng.gen_range_usize(1, 100);
        // Pick density
        let p = match rng.gen_range_usize(0, 4) {
            0 => 1, // sparse
            1 => 2,
            2 => 4,
            _ => 3,
        };
        let a: Vec<i32> = (0..n).map(|_| if rng.gen_range_usize(0, 9) < p { 1 } else { 0 }).collect();
        emit(a, &mut seen, &mut out, &mut count);
    }
}

