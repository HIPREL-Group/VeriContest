use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_k: i32,
    seed_lefts: &Vec<i32>,
    seed_spans: &Vec<i32>,
    mutation_kind: u8,
) -> (result: (i32, Vec<i32>, Vec<i32>))
    requires
        1 <= seed_k <= 100_000,
        1 <= seed_lefts.len() <= 100_000,
        seed_lefts.len() == seed_spans.len(),
        forall|i: int| 0 <= i < seed_lefts.len() ==> 1 <= #[trigger] seed_lefts[i] <= 100_000,
        forall|i: int| 0 <= i < seed_spans.len() ==> 0 <= #[trigger] seed_spans[i] <= 99_999,
    ensures
        1 <= result.0 <= 100_000,
        1 <= result.1.len() == result.2.len() <= 100_000,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= result.2[i] <= 100_000,
{
    // Mutate k
    let k: i32 = if mutation_kind == 0 {
        seed_k
    } else if mutation_kind == 1 && seed_k < 100_000 {
        seed_k + 1
    } else if mutation_kind == 2 && seed_k > 1 {
        seed_k - 1
    } else if mutation_kind == 3 {
        1
    } else if mutation_kind == 4 {
        100_000
    } else if mutation_kind == 5 {
        if seed_k <= 50_000 { seed_k * 2 } else { seed_k }
    } else if mutation_kind == 6 {
        seed_k / 2 + 1
    } else {
        seed_k
    };

    let n: usize = seed_lefts.len();
    let mut lefts: Vec<i32> = Vec::new();
    let mut rights: Vec<i32> = Vec::new();
    let mut idx: usize = 0;

    while idx < n
        invariant
            n == seed_lefts.len(),
            n == seed_spans.len(),
            1 <= n <= 100_000,
            0 <= idx <= n,
            lefts.len() == idx,
            rights.len() == idx,
            forall|j: int| 0 <= j < seed_lefts.len() ==> 1 <= #[trigger] seed_lefts[j] <= 100_000,
            forall|j: int| 0 <= j < seed_spans.len() ==> 0 <= #[trigger] seed_spans[j] <= 99_999,
            forall|j: int| 0 <= j < idx as int ==> 1 <= #[trigger] lefts[j] <= rights[j] <= 100_000,
        decreases n - idx,
    {
        let l = seed_lefts[idx];
        let span = seed_spans[idx];
        let r_raw = l + span;
        let r: i32 = if r_raw > 100_000 { 100_000 } else { r_raw };
        assert(1 <= l <= r <= 100_000) by {}
        lefts.push(l);
        rights.push(r);
        idx = idx + 1;
    }

    (k, lefts, rights)
}

}

use std::io::Write;
use std::collections::HashSet;

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
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

fn build_input(k: i32, lefts: &[i32], rights: &[i32]) -> String {
    let t = lefts.len();
    let mut s = format!("{} {}\n", t, k);
    for i in 0..t {
        s.push_str(&format!("{} {}\n", lefts[i], rights[i]));
    }
    s
}

fn build_output(answers: &[i32]) -> String {
    let mut s = String::new();
    for &a in answers {
        s.push_str(&format!("{}\n", a));
    }
    s
}

fn main() {
    let target_count: usize = 100;
    let mut rng = Rng::new(474);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |k: i32, lefts: Vec<i32>, rights: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        if lefts.is_empty() || k < 1 { return; }
        for i in 0..lefts.len() {
            if lefts[i] < 1 || rights[i] < lefts[i] || rights[i] > 100_000 { return; }
        }
        let key = format!("{}_{:?}_{:?}", k, lefts, rights);
        if !seen.insert(key) { return; }
        let result = Solution::solve_queries(k, lefts.clone(), rights.clone());
        let inp = build_input(k, &lefts, &rights);
        let outp = build_output(&result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    emit(2, vec![1, 2, 4], vec![3, 3, 4], &mut seen, &mut out, &mut count);
    emit(1, vec![1], vec![1], &mut seen, &mut out, &mut count);
    emit(100_000, vec![1, 100_000], vec![100_000, 100_000], &mut seen, &mut out, &mut count);
    emit(1, vec![1, 1], vec![1, 100_000], &mut seen, &mut out, &mut count);
    emit(2, vec![1], vec![100_000], &mut seen, &mut out, &mut count);
    emit(5, vec![1, 50, 100], vec![100, 100, 100], &mut seen, &mut out, &mut count);

    while count < target_count {
        let t = rng.gen_range_usize(1, 50);
        let k = rng.gen_range_i64(1, 100) as i32;
        let mut lefts = Vec::with_capacity(t);
        let mut rights = Vec::with_capacity(t);
        for _ in 0..t {
            let l = rng.gen_range_i64(1, 100_000) as i32;
            let r_max = (l as i64 + 1000).min(100_000);
            let r = rng.gen_range_i64(l as i64, r_max) as i32;
            lefts.push(l);
            rights.push(r);
        }
        emit(k, lefts, rights, &mut seen, &mut out, &mut count);
    }
}

