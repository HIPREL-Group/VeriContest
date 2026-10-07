use vstd::prelude::*;

verus! {

pub fn generate_test_case(flowers: Vec<i64>, mutation_kind: u8) -> (result: Vec<i64>)
    requires
        2 <= flowers.len() <= 200_000,
        forall|i: int| 0 <= i < flowers.len() ==> 1 <= #[trigger] flowers[i] <= 1_000_000_000,
    ensures
        2 <= result.len() <= 200_000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        flowers
    } else if mutation_kind == 1 {
        // set first element to 1 (min boundary)
        let mut d = flowers;
        d.set(0, 1);
        d
    } else if mutation_kind == 2 {
        // set first element to 1_000_000_000 (max boundary)
        let mut d = flowers;
        d.set(0, 1_000_000_000);
        d
    } else if mutation_kind == 3 {
        // nudge first element up (if < max)
        let mut d = flowers;
        if d[0] < 1_000_000_000 {
            d.set(0, d[0] + 1);
        }
        d
    } else if mutation_kind == 4 {
        // nudge first element down (if > 1)
        let mut d = flowers;
        if d[0] > 1 {
            d.set(0, d[0] - 1);
        }
        d
    } else if mutation_kind == 5 {
        // set all elements to 1
        let mut d = flowers;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == flowers.len(),
                2 <= d.len() <= 200_000,
                forall|j: int| 0 <= j < i ==> d[j] == 1i64,
                forall|j: int| i <= j < d.len() ==> d[j] == flowers[j],
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        d
    } else if mutation_kind == 6 {
        // set all elements to 1_000_000_000
        let mut d = flowers;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == flowers.len(),
                2 <= d.len() <= 200_000,
                forall|j: int| 0 <= j < i ==> d[j] == 1_000_000_000i64,
                forall|j: int| i <= j < d.len() ==> d[j] == flowers[j],
            decreases d.len() - i,
        {
            d.set(i, 1_000_000_000);
            i += 1;
        }
        d
    } else if mutation_kind == 7 && flowers.len() < 200_000 {
        // grow by one element
        let mut d = flowers;
        d.push(1);
        d
    } else if mutation_kind == 8 && flowers.len() > 2 {
        // shrink by one element
        let mut d = flowers;
        d.pop();
        d
    } else if mutation_kind == 9 {
        // swap first two elements
        let mut d = flowers;
        let tmp = d[0];
        d.set(0, d[1]);
        d.set(1, tmp);
        d
    } else {
        // fallback
        flowers
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

fn build_input(flowers: &[i64]) -> String {
    let mut s = format!("{}\n", flowers.len());
    let parts: Vec<String> = flowers.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
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

    emit(vec![1, 2], &mut seen, &mut out, &mut count);
    emit(vec![1, 4, 5], &mut seen, &mut out, &mut count);
    emit(vec![3, 1, 2, 3, 1], &mut seen, &mut out, &mut count);
    emit(vec![5, 5], &mut seen, &mut out, &mut count);
    emit(vec![1, 1, 1, 1, 1], &mut seen, &mut out, &mut count);
    emit(vec![1, 1_000_000_000], &mut seen, &mut out, &mut count);

    let mut tries = 0usize;
    while count < target {
        tries += 1;
        if tries > 100000 { break; }
        let n = match tries % 5 {
            0 => 2,
            1 => rng.gen_range_usize(2, 5),
            2 => rng.gen_range_usize(5, 50),
            3 => rng.gen_range_usize(50, 500),
            _ => rng.gen_range_usize(500, 5000),
        };
        let max_v = match tries % 3 {
            0 => 5,
            1 => 100,
            _ => 1_000_000_000,
        };
        let flowers: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, max_v)).collect();
        emit(flowers, &mut seen, &mut out, &mut count);
    }
}

