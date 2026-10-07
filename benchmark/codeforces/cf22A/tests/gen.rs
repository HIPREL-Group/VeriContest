use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    raw_a: Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, usize))
    requires
        1 <= raw_a.len() <= 100,
        forall|i: int| 0 <= i < raw_a.len() ==> -100 <= #[trigger] raw_a[i] as int <= 100,
    ensures
        1 <= result.1 <= 100,
        result.0.len() == result.1,
        forall|i: int| 0 <= i < result.0.len() ==> -100 <= #[trigger] result.0[i] as int <= 100,
{
    let n = raw_a.len();
    if mutation_kind == 0 {
        (raw_a, n)
    } else if mutation_kind == 1 {
        let mut a = raw_a;
        let mut i: usize = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                a.len() == n,
                1 <= n <= 100,
                forall|j: int| 0 <= j < i ==> a[j] == 0i32,
                forall|j: int| i <= j < a.len() ==> -100 <= #[trigger] a[j] as int <= 100,
            decreases a.len() - i,
        {
            a.set(i, 0i32);
            i += 1;
        }
        (a, n)
    } else if mutation_kind == 2 {
        let mut a = raw_a;
        let mut i: usize = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                a.len() == n,
                1 <= n <= 100,
                forall|j: int| 0 <= j < i ==> a[j] == 100i32,
                forall|j: int| i <= j < a.len() ==> -100 <= #[trigger] a[j] as int <= 100,
            decreases a.len() - i,
        {
            a.set(i, 100i32);
            i += 1;
        }
        (a, n)
    } else if mutation_kind == 3 && raw_a.len() > 1 {
        let mut a = raw_a;
        a.pop();
        let new_n = a.len();
        (a, new_n)
    } else {
        (raw_a, n)
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
        let range = (hi - lo + 1) as u64;
        lo + (self.next_u64() % range) as i64
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

fn build_input(a: &Vec<i32>) -> String {
    let n = a.len();
    let mut s = format!("{}\n", n);
    for i in 0..n {
        if i > 0 { s.push(' '); }
        s.push_str(&format!("{}", a[i]));
    }
    s.push('\n');
    s
}

fn build_output(ans: &Option<i32>) -> String {
    match ans {
        Some(v) => format!("{}\n", v),
        None => "NO\n".to_string(),
    }
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(22);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |a: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let n = a.len();
        if n < 1 || n > 100 { return; }
        for v in &a { if !(*v >= -100 && *v <= 100) { return; } }
        let inp = build_input(&a);
        if !seen.insert(inp.clone()) { return; }
        let ans = Solution::second_min(a, n);
        let outp = build_output(&ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // Sample tests
    emit(vec![1, 2, 2, -4], &mut seen, &mut out, &mut count);
    emit(vec![1, 2, 3, 1, 1], &mut seen, &mut out, &mut count);
    emit(vec![5], &mut seen, &mut out, &mut count);
    emit(vec![5, 5, 5], &mut seen, &mut out, &mut count);

    // Boundary
    emit(vec![-100, 100], &mut seen, &mut out, &mut count);
    emit(vec![100, -100], &mut seen, &mut out, &mut count);
    emit(vec![0; 50], &mut seen, &mut out, &mut count);

    // Random
    let mut tries = 0usize;
    while count < target && tries < target * 200 {
        tries += 1;
        let n = match tries % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(5, 20),
            2 => rng.gen_range_usize(20, 50),
            3 => rng.gen_range_usize(50, 100),
            _ => rng.gen_range_usize(1, 100),
        };
        let a: Vec<i32> = (0..n).map(|_| rng.gen_range_i64(-100, 100) as i32).collect();
        emit(a, &mut seen, &mut out, &mut count);
    }
}
