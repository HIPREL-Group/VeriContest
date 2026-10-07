use vstd::prelude::*;

verus! {

pub fn generate_test_case(a: Vec<i64>, mutation_kind: u8) -> (result: Vec<i64>)
    requires
        1 <= a.len() <= 200_000,
        forall|k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= 10_000,
    ensures
        1 <= result.len() <= 200_000,
        forall|k: int| 0 <= k < result.len() ==> 1 <= #[trigger] result[k] <= 10_000,
{
    if mutation_kind == 0 {
        a
    } else if mutation_kind == 1 {
        let mut r = a;
        let last = r.len() - 1;
        r.set(last, 1);
        r
    } else if mutation_kind == 2 {
        let mut r = a;
        let last = r.len() - 1;
        r.set(last, 10_000);
        r
    } else if mutation_kind == 3 && a[a.len() - 1] < 10_000 {
        let mut r = a;
        let last = r.len() - 1;
        r.set(last, r[last] + 1);
        r
    } else if mutation_kind == 4 && a[a.len() - 1] > 1 {
        let mut r = a;
        let last = r.len() - 1;
        r.set(last, r[last] - 1);
        r
    } else if mutation_kind == 5 && a.len() < 200_000 {
        let mut r = a;
        r.push(1);
        r
    } else if mutation_kind == 6 && a.len() > 1 {
        let mut r = a;
        r.pop();
        r
    } else if mutation_kind == 7 {
        let mut r = a;
        let mut i: usize = 0;
        while i < r.len()
            invariant
                0 <= i <= r.len(),
                r.len() == a.len(),
                1 <= r.len() <= 200_000,
                forall|j: int| 0 <= j < i ==> r[j] == 1i64,
                forall|j: int| i <= j < r.len() ==> r[j] == a[j],
            decreases r.len() - i,
        {
            r.set(i, 1);
            i += 1;
        }
        r
    } else if mutation_kind == 8 {
        let mut r = a;
        let mut i: usize = 0;
        while i < r.len()
            invariant
                0 <= i <= r.len(),
                r.len() == a.len(),
                1 <= r.len() <= 200_000,
                forall|j: int| 0 <= j < i ==> r[j] == 10_000i64,
                forall|j: int| i <= j < r.len() ==> r[j] == a[j],
            decreases r.len() - i,
        {
            r.set(i, 10_000);
            i += 1;
        }
        r
    } else {
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
    let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(ans: i32) -> String { format!("{}\n", ans) }

fn random_array(rng: &mut Rng, len: usize, max_val: i64) -> Vec<i64> {
    (0..len).map(|_| rng.gen_range_i64(1, max_val)).collect()
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let mut seen: HashSet<u64> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |a: Vec<i64>, seen: &mut HashSet<u64>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let mut h: u64 = 1469598103934665603;
        h ^= a.len() as u64;
        h = h.wrapping_mul(1099511628211);
        for &x in &a { h ^= x as u64; h = h.wrapping_mul(1099511628211); }
        if !seen.insert(h) { return; }
        let inp = build_input(&a);
        let ans = Solution::count_equal_sums(a);
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Examples
    emit(vec![5,5,4,5,5,5,6], &mut seen, &mut out, &mut count);
    emit(vec![4,8,8,7,8,4,4,5], &mut seen, &mut out, &mut count);
    emit(vec![1,4,3,3], &mut seen, &mut out, &mut count);

    // Edge cases
    emit(vec![1], &mut seen, &mut out, &mut count);
    emit(vec![1,1], &mut seen, &mut out, &mut count);
    emit(vec![1,2], &mut seen, &mut out, &mut count);
    emit(vec![1,2,1], &mut seen, &mut out, &mut count);
    emit(vec![1,1,1,1], &mut seen, &mut out, &mut count);
    emit(vec![10_000; 5], &mut seen, &mut out, &mut count);

    while count < target {
        let n = match count % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(5, 50),
            3 => rng.gen_range_usize(20, 200),
            _ => rng.gen_range_usize(100, 1000),
        };
        let max_val = match count % 4 {
            0 => 10i64,
            1 => 100,
            2 => 1_000,
            _ => 10_000,
        };
        let v = random_array(&mut rng, n, max_val);
        emit(v, &mut seen, &mut out, &mut count);
    }
}

