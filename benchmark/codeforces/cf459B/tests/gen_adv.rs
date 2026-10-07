use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    fillers: &Vec<i64>,
) -> (flowers: Vec<i64>)
    requires
        2 <= fillers.len() <= 200_000,
        forall|i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 1_000_000_000,
    ensures
        2 <= flowers.len() <= 200_000,
        forall|i: int| 0 <= i < flowers.len() ==> 1 <= #[trigger] flowers[i] <= 1_000_000_000,
{
    let mut flowers: Vec<i64> = Vec::new();
    let n = fillers.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == fillers.len(),
            2 <= n <= 200_000,
            0 <= i <= n,
            flowers.len() == i,
            forall|k: int| 0 <= k < fillers.len() ==> 1 <= #[trigger] fillers[k] <= 1_000_000_000,
            forall|k: int| 0 <= k < i as int ==> 1 <= #[trigger] flowers[k] <= 1_000_000_000,
        decreases n - i,
    {
        flowers.push(fillers[i]);
        i += 1;
    }
    flowers
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

fn build_input(flowers: &[i64]) -> String {
    let mut s = format!("{}\n", flowers.len());
    let parts: Vec<String> = flowers.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |flowers: Vec<i64>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let n = flowers.len();
        if !(2 <= n && n <= 200_000) { return; }
        for &v in &flowers { if !(1 <= v && v <= 1_000_000_000) { return; } }
        let key = format!("{:?}", flowers);
        if !seen.insert(key) { return; }
        let inp = build_input(&flowers);
        let (d, p) = Solution::max_beauty_and_pair_count(flowers.clone());
        let outs = format!("{} {}\n", d, p);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    let mut tries = 0usize;
    while count < target {
        tries += 1;
        if tries > 100000 { break; }
        let mode = tries % 10;
        let n = match mode {
            0 => 2,
            1 => 200_000,
            2 => 100_000,
            3 => rng.gen_range_usize(2, 20),
            4 => rng.gen_range_usize(50, 500),
            5 => rng.gen_range_usize(500, 5000),
            _ => rng.gen_range_usize(2, 1000),
        };
        let flowers: Vec<i64> = match mode {
            0 => vec![1, 1_000_000_000],
            1 => vec![5; n],
            2 => vec![1_000_000_000; n],
            3 => (0..n).map(|i| if i % 2 == 0 { 1 } else { 1_000_000_000 }).collect(),
            4 => (0..n).map(|_| rng.gen_range_i64(1, 100)).collect(),
            5 => (0..n).map(|_| rng.gen_range_i64(1, 1_000_000_000)).collect(),
            6 => {
                let mut v = vec![1; n / 2 + 1];
                v.extend((0..n - v.len()).map(|_| 1_000_000_000));
                v
            }
            _ => (0..n).map(|_| rng.gen_range_i64(1, 10)).collect(),
        };
        emit(flowers, &mut seen, &mut out, &mut count);
    }
}

