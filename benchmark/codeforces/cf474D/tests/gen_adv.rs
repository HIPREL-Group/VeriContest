use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    k: i32,
    lefts_in: &Vec<i32>,
    rights_in: &Vec<i32>,
) -> (res: (i32, Vec<i32>, Vec<i32>))
    requires
        1 <= k <= 100_000,
        1 <= lefts_in.len() == rights_in.len() <= 100_000,
        forall|i: int|
            0 <= i < lefts_in.len() ==> 1 <= #[trigger] lefts_in[i] <= rights_in[i] <= 100_000,
    ensures
        1 <= res.0 <= 100_000,
        1 <= res.1.len() == res.2.len() <= 100_000,
        forall|i: int|
            0 <= i < res.1.len() ==> 1 <= #[trigger] res.1[i] <= res.2[i] <= 100_000,
{
    let n = lefts_in.len();
    let mut lefts: Vec<i32> = Vec::new();
    let mut rights: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == lefts_in.len(),
            n == rights_in.len(),
            1 <= n <= 100_000,
            i <= n,
            lefts.len() == i,
            rights.len() == i,
            forall|j: int| 0 <= j < lefts_in.len() ==> 1 <= #[trigger] lefts_in[j] <= rights_in[j] <= 100_000,
            forall|j: int| 0 <= j < i as int ==> 1 <= #[trigger] lefts[j] <= rights[j] <= 100_000,
            forall|j: int| 0 <= j < i as int ==> #[trigger] lefts[j] == lefts_in[j],
            forall|j: int| 0 <= j < i as int ==> #[trigger] rights[j] == rights_in[j],
        decreases n - i,
    {
        lefts.push(lefts_in[i]);
        rights.push(rights_in[i]);
        i = i + 1;
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
    let target_count: usize = 200;
    let mut rng = Rng::new(47402);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
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

    // Adversarial: max queries for k=1
    let lefts1: Vec<i32> = (1..=1000).map(|i| i).collect();
    let rights1: Vec<i32> = (1..=1000).map(|_| 100_000).collect();
    emit(1, lefts1, rights1, &mut seen, &mut out, &mut count);

    // k=100000 (no white groups possible except at exact length 100000)
    let lefts2: Vec<i32> = (1..=100).map(|i| i * 1000).collect();
    let rights2: Vec<i32> = (1..=100).map(|_| 100_000).collect();
    emit(100_000, lefts2, rights2, &mut seen, &mut out, &mut count);

    // Many same-pair queries
    emit(2, vec![1; 100], vec![100_000; 100], &mut seen, &mut out, &mut count);
    emit(3, vec![1; 100], vec![100_000; 100], &mut seen, &mut out, &mut count);

    while count < target_count {
        let t = match count % 5 {
            0 => rng.gen_range_usize(500, 2000),
            1 => rng.gen_range_usize(100, 500),
            2 => rng.gen_range_usize(50, 200),
            3 => rng.gen_range_usize(10, 100),
            _ => rng.gen_range_usize(1, 50),
        };
        let k = match count % 4 {
            0 => 1,
            1 => 2,
            2 => rng.gen_range_i64(1, 100) as i32,
            _ => rng.gen_range_i64(1, 100_000) as i32,
        };
        let mut lefts = Vec::with_capacity(t);
        let mut rights = Vec::with_capacity(t);
        for _ in 0..t {
            let l = rng.gen_range_i64(1, 100_000) as i32;
            let r = rng.gen_range_i64(l as i64, 100_000) as i32;
            lefts.push(l);
            rights.push(r);
        }
        emit(k, lefts, rights, &mut seen, &mut out, &mut count);
    }
}

