use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    a_start: i64,
    b_fixed: i64,
) -> (exams: Vec<(i64, i64)>)
    requires
        1 <= n <= 5000,
        1 <= b_fixed <= 100,
        b_fixed + 1 <= a_start,
        a_start + (n as i64) <= 1_000_000_000,
    ensures
        exams.len() == n,
        exams.len() >= 1,
        exams.len() <= 5000,
        forall|i: int| 0 <= i < exams.len() ==> 1 <= (#[trigger] exams[i]).1 < exams[i].0 <= 1_000_000_000,
        forall|i: int, j: int| 0 <= i < j < exams.len() ==>
            #[trigger] exams[i].0 < #[trigger] exams[j].0
            || (exams[i].0 == exams[j].0 && exams[i].1 <= exams[j].1),
{
    let mut exams: Vec<(i64, i64)> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            0 <= i <= n,
            1 <= n <= 5000,
            1 <= b_fixed <= 100,
            b_fixed + 1 <= a_start,
            a_start + (n as i64) <= 1_000_000_000,
            exams.len() == i,
            forall|k: int| 0 <= k < i as int ==>
                #[trigger] exams[k].0 == a_start + (k as i64)
                && exams[k].1 == b_fixed,
        decreases n - i,
    {
        let a_val: i64 = a_start + (i as i64);
        let b_val: i64 = b_fixed;

        assert(a_val >= a_start);
        assert(a_val <= a_start + (n as i64));
        assert(a_val <= 1_000_000_000);
        assert(b_val < a_val);

        exams.push((a_val, b_val));
        i = i + 1;
    }

    proof {
        assert forall|k: int| 0 <= k < exams.len() implies
            1 <= (#[trigger] exams[k]).1 < exams[k].0 <= 1_000_000_000
        by {
            assert(exams[k].0 == a_start + (k as i64));
            assert(exams[k].1 == b_fixed);
            assert(a_start + (k as i64) <= a_start + (n as i64));
        }

        assert forall|i1: int, j1: int| 0 <= i1 < j1 < exams.len() implies
            #[trigger] exams[i1].0 < #[trigger] exams[j1].0
            || (exams[i1].0 == exams[j1].0 && exams[i1].1 <= exams[j1].1)
        by {
            assert(exams[i1].0 == a_start + (i1 as i64));
            assert(exams[j1].0 == a_start + (j1 as i64));
        }
    }

    exams
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

fn build_input(exams: &[(i64, i64)]) -> String {
    let mut s = format!("{}\n", exams.len());
    for (a, b) in exams {
        s.push_str(&format!("{} {}\n", a, b));
    }
    s
}

fn main() {
    let target_count: usize = 200;
    let mut rng = Rng::new(47903);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |exams: Vec<(i64, i64)>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        if exams.is_empty() { return; }
        for (a, b) in &exams {
            if *b < 1 || *a <= *b || *a > 1_000_000_000 { return; }
        }
        let key = format!("{:?}", exams);
        if !seen.insert(key) { return; }
        let mut sorted = exams.clone();
        sorted.sort();
        let result = Solution::min_last_exam_day(sorted);
        let inp = build_input(&exams);
        let outp = format!("{}\n", result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // Adversarial: max n
    let max_exams: Vec<(i64, i64)> = (1..=5000).map(|i| (i + 1, i)).collect();
    emit(max_exams, &mut seen, &mut out, &mut count);

    let max_rev: Vec<(i64, i64)> = (1..=5000).rev().map(|i| (i + 5001, i)).collect();
    emit(max_rev, &mut seen, &mut out, &mut count);

    // All same a
    let same_a: Vec<(i64, i64)> = (1..=5000).map(|i| (1_000_000_000, i)).collect();
    emit(same_a, &mut seen, &mut out, &mut count);

    // Adversarial: forces b < last_day each time
    let mut adv = Vec::new();
    for i in 0..5000 {
        adv.push((i + 1000, 1));
    }
    emit(adv, &mut seen, &mut out, &mut count);

    while count < target_count {
        let n = match count % 5 {
            0 | 1 => rng.gen_range_usize(2000, 5000),
            2 => rng.gen_range_usize(500, 2000),
            3 => rng.gen_range_usize(100, 1000),
            _ => rng.gen_range_usize(10, 200),
        };
        let mut exams = Vec::with_capacity(n);
        for _ in 0..n {
            let a = rng.gen_range_i64(2, 1_000_000_000);
            let b = rng.gen_range_i64(1, a - 1);
            exams.push((a, b));
        }
        emit(exams, &mut seen, &mut out, &mut count);
    }
}

