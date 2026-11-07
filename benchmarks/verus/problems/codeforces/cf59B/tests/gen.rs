use vstd::prelude::*;

verus! {

pub fn generate_test_case(a: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= a.len() <= 100,
        forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 100,
    ensures
        1 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100,
{
    if mutation_kind == 0 {
        // identity
        a
    } else if mutation_kind == 1 {
        // set all elements to 1 (all odd)
        let n = a.len();
        let mut y = a;
        let mut i: usize = 0;
        while i < n
            invariant
                1 <= n <= 100,
                y.len() == n,
                0 <= i <= n,
                forall|j: int| 0 <= j < i ==> (#[trigger] y[j] == 1),
                forall|j: int| i <= j < n as int ==> 1 <= (#[trigger] y[j] as int) <= 100,
            decreases n - i,
        {
            y.set(i, 1i32);
            i += 1;
        }
        assert forall|j: int| 0 <= j < y.len() implies 1 <= (#[trigger] y[j] as int) <= 100 by {}
        y
    } else if mutation_kind == 2 {
        // set all elements to 2 (all even)
        let n = a.len();
        let mut y = a;
        let mut i: usize = 0;
        while i < n
            invariant
                1 <= n <= 100,
                y.len() == n,
                0 <= i <= n,
                forall|j: int| 0 <= j < i ==> (#[trigger] y[j] == 2),
                forall|j: int| i <= j < n as int ==> 1 <= (#[trigger] y[j] as int) <= 100,
            decreases n - i,
        {
            y.set(i, 2i32);
            i += 1;
        }
        assert forall|j: int| 0 <= j < y.len() implies 1 <= (#[trigger] y[j] as int) <= 100 by {}
        y
    } else if mutation_kind == 3 {
        // set all elements to 100 (boundary max, even)
        let n = a.len();
        let mut y = a;
        let mut i: usize = 0;
        while i < n
            invariant
                1 <= n <= 100,
                y.len() == n,
                0 <= i <= n,
                forall|j: int| 0 <= j < i ==> (#[trigger] y[j] == 100),
                forall|j: int| i <= j < n as int ==> 1 <= (#[trigger] y[j] as int) <= 100,
            decreases n - i,
        {
            y.set(i, 100i32);
            i += 1;
        }
        assert forall|j: int| 0 <= j < y.len() implies 1 <= (#[trigger] y[j] as int) <= 100 by {}
        y
    } else if mutation_kind == 4 {
        // set all elements to 99 (boundary max odd)
        let n = a.len();
        let mut y = a;
        let mut i: usize = 0;
        while i < n
            invariant
                1 <= n <= 100,
                y.len() == n,
                0 <= i <= n,
                forall|j: int| 0 <= j < i ==> (#[trigger] y[j] == 99),
                forall|j: int| i <= j < n as int ==> 1 <= (#[trigger] y[j] as int) <= 100,
            decreases n - i,
        {
            y.set(i, 99i32);
            i += 1;
        }
        assert forall|j: int| 0 <= j < y.len() implies 1 <= (#[trigger] y[j] as int) <= 100 by {}
        y
    } else if mutation_kind == 5 && a.len() >= 1 {
        // flip first element: 101 - val (maps [1,100] -> [1,100])
        let mut y = a;
        let old = y[0];
        let new_val = 101i32 - old;
        assert(1 <= new_val <= 100);
        y.set(0, new_val);
        assert forall|j: int| 0 <= j < y.len() implies 1 <= (#[trigger] y[j] as int) <= 100 by {
            assert(1 <= y[0] as int <= 100);
        }
        y
    } else if mutation_kind == 6 && a.len() >= 1 {
        // flip last element: 101 - val
        let mut y = a;
        let last = y.len() - 1;
        let old = y[last];
        let new_val = 101i32 - old;
        assert(1 <= new_val <= 100);
        y.set(last, new_val);
        assert forall|j: int| 0 <= j < y.len() implies 1 <= (#[trigger] y[j] as int) <= 100 by {}
        y
    } else if mutation_kind == 7 && a.len() >= 2 {
        // swap first two elements
        let mut y = a;
        let v0 = y[0];
        let v1 = y[1];
        y.set(0, v1);
        y.set(1, v0);
        assert forall|j: int| 0 <= j < y.len() implies 1 <= (#[trigger] y[j] as int) <= 100 by {}
        y
    } else if mutation_kind == 8 && a.len() >= 1 {
        // set first element to 1 (min boundary)
        let mut y = a;
        y.set(0, 1i32);
        assert forall|j: int| 0 <= j < y.len() implies 1 <= (#[trigger] y[j] as int) <= 100 by {
            assert(1 <= y[0] as int <= 100);
        }
        y
    } else if mutation_kind == 9 && a.len() >= 1 {
        // set first element to 100 (max boundary)
        let mut y = a;
        y.set(0, 100i32);
        assert forall|j: int| 0 <= j < y.len() implies 1 <= (#[trigger] y[j] as int) <= 100 by {
            assert(1 <= y[0] as int <= 100);
        }
        y
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
    let mut rng = Rng::new(59);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
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

    // Examples
    emit(vec![1], &mut seen, &mut out, &mut count);
    emit(vec![2], &mut seen, &mut out, &mut count);
    emit(vec![5, 6, 7], &mut seen, &mut out, &mut count);

    // Edges
    emit(vec![1; 100], &mut seen, &mut out, &mut count);
    emit(vec![100], &mut seen, &mut out, &mut count);
    emit(vec![100; 100], &mut seen, &mut out, &mut count);
    emit(vec![2, 4, 6, 8], &mut seen, &mut out, &mut count); // all even
    emit(vec![3, 5, 7], &mut seen, &mut out, &mut count); // all odd
    emit(vec![1, 2], &mut seen, &mut out, &mut count);
    emit(vec![2, 3], &mut seen, &mut out, &mut count);

    while count < target {
        let n = rng.gen_range_usize(1, 100);
        let max_v = match rng.gen_range_usize(0, 3) {
            0 => 5,
            1 => 20,
            _ => 100,
        };
        let a: Vec<i32> = (0..n).map(|_| rng.gen_range_i64(1, max_v) as i32).collect();
        emit(a, &mut seen, &mut out, &mut count);
    }
}

