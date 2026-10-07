use vstd::prelude::*;

verus! {

pub open spec fn sum_maxima(maxima: Seq<i64>, end: int) -> int
    recommends 0 <= end <= maxima.len(),
    decreases end,
{
    if end <= 0 {
        0
    } else {
        sum_maxima(maxima, end - 1) + maxima[end - 1] as int
    }
}

pub proof fn sum_maxima_bound(maxima: Seq<i64>, end: int)
    requires
        0 <= end <= maxima.len(),
        forall|i: int| 0 <= i < maxima.len() ==> 1 <= #[trigger] maxima[i] <= 1_000_000,
    ensures
        end <= sum_maxima(maxima, end) <= end * 1_000_000,
    decreases end,
{
    if end <= 0 {
    } else {
        sum_maxima_bound(maxima, end - 1);
    }
}

pub fn generate_test_case(
    n: usize,
    extra_total: i64,
    maxima_in: Vec<i64>,
) -> (res: (i64, Vec<i64>))
    requires
        1 <= n <= 200_000,
        maxima_in.len() == n,
        forall|i: int| 0 <= i < maxima_in.len() ==> 1 <= #[trigger] maxima_in[i] <= 1_000_000,
        0 <= extra_total,
        extra_total as int <= sum_maxima(maxima_in@, n as int) - n as int,
    ensures
        res.1.len() == n,
        1 <= res.1.len() <= 200_000,
        forall|i: int| 0 <= i < res.1.len() ==> 1 <= #[trigger] res.1[i] <= 1_000_000,
        res.1.len() as int <= res.0 as int <= sum_maxima(res.1@, res.1.len() as int),
        res.0 as int == n as int + extra_total as int,
{
    proof {
        sum_maxima_bound(maxima_in@, n as int);
    }
    let total: i64 = (n as i64) + extra_total;
    (total, maxima_in)
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

fn build_input(total: i64, maxima: &[i64]) -> String {
    let n = maxima.len();
    let mut s = format!("{} {}\n", n, total);
    let parts: Vec<String> = maxima.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(ans: &[i64]) -> String {
    let parts: Vec<String> = ans.iter().map(|x| x.to_string()).collect();
    format!("{}\n", parts.join(" "))
}

fn main() {
    let target_count: usize = 200;
    let mut rng = Rng::new(53404);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |total: i64, maxima: Vec<i64>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        let n = maxima.len();
        if n < 1 { return; }
        let sum: i64 = maxima.iter().sum();
        if total < n as i64 || total > sum { return; }
        for &d in &maxima { if d < 1 || d > 1_000_000 { return; } }
        let key = format!("{}_{:?}", total, maxima);
        if !seen.insert(key) { return; }
        let result = Solution::impossible_face_counts(total, maxima.clone());
        let inp = build_input(total, &maxima);
        let outp = build_output(&result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // Adversarial: max n=200000
    let max_n = 200_000;
    let max_dice = vec![1_000_000i64; max_n];
    let max_sum: i64 = max_dice.iter().sum();
    emit(max_n as i64, max_dice.clone(), &mut seen, &mut out, &mut count);
    emit(max_sum, max_dice.clone(), &mut seen, &mut out, &mut count);
    emit(max_sum / 2, max_dice.clone(), &mut seen, &mut out, &mut count);

    // n=1, large dice
    emit(1, vec![1_000_000], &mut seen, &mut out, &mut count);
    emit(500_000, vec![1_000_000], &mut seen, &mut out, &mut count);
    emit(1_000_000, vec![1_000_000], &mut seen, &mut out, &mut count);

    // All 1s
    emit(100_000, vec![1; 100_000], &mut seen, &mut out, &mut count);

    while count < target_count {
        let n = match count % 5 {
            0 | 1 => rng.gen_range_usize(50_000, 200_000),
            2 => rng.gen_range_usize(10_000, 50_000),
            3 => rng.gen_range_usize(1000, 10_000),
            _ => rng.gen_range_usize(2, 1000),
        };
        let avg = rng.gen_range_i64(1, 1_000_000);
        let maxima: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, avg.max(1)) as i64).collect();
        let sum: i64 = maxima.iter().sum();
        if (n as i64) > sum { continue; }
        let total = rng.gen_range_i64(n as i64, sum);
        emit(total, maxima, &mut seen, &mut out, &mut count);
    }
}

