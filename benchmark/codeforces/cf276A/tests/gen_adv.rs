use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    fs: &Vec<i64>,
    ts: &Vec<i64>,
    k: i64,
) -> (result: (Vec<(i64, i64)>, i64))
    requires
        fs.len() == ts.len(),
        fs.len() >= 1,
        fs.len() <= 10000,
        1 <= k <= 1000000000,
        forall |i: int| 0 <= i < fs.len() ==> 1 <= #[trigger] fs[i] <= 1000000000,
        forall |i: int| 0 <= i < ts.len() ==> 1 <= #[trigger] ts[i] <= 1000000000,
    ensures
        result.0.len() >= 1,
        result.0.len() <= 10000,
        1 <= result.1 <= 1000000000,
        result.1 == k,
        forall |i: int| 0 <= i < result.0.len() ==>
            1 <= #[trigger] result.0@[i].0 <= 1000000000,
        forall |i: int| 0 <= i < result.0.len() ==>
            1 <= #[trigger] result.0@[i].1 <= 1000000000,
{
    let n = fs.len();
    let mut restaurants: Vec<(i64, i64)> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            n == fs.len(),
            fs.len() == ts.len(),
            restaurants.len() == i,
            0 <= i <= n,
            forall |j: int| 0 <= j < fs.len() ==> 1 <= #[trigger] fs[j] <= 1000000000,
            forall |j: int| 0 <= j < ts.len() ==> 1 <= #[trigger] ts[j] <= 1000000000,
            forall |j: int| 0 <= j < i as int ==>
                #[trigger] restaurants@[j].0 == fs[j] && restaurants@[j].1 == ts[j],
            forall |j: int| 0 <= j < i as int ==>
                1 <= #[trigger] restaurants@[j].0 <= 1000000000,
            forall |j: int| 0 <= j < i as int ==>
                1 <= #[trigger] restaurants@[j].1 <= 1000000000,
        decreases n - i,
    {
        let f = fs[i];
        let t = ts[i];
        restaurants.push((f, t));
        i = i + 1;
    }

    (restaurants, k)
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

fn build_input(restaurants: &[(i64, i64)], k: i64) -> String {
    let mut s = format!("{} {}\n", restaurants.len(), k);
    for &(f, t) in restaurants {
        s.push_str(&format!("{} {}\n", f, t));
    }
    s
}

fn build_output(ans: i64) -> String {
    format!("{}\n", ans)
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(0x276AA);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut tries = 0;
    while count < target && tries < target * 100 {
        tries += 1;
        let n = match tries % 6 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(2, 30),
            2 => rng.gen_range_usize(30, 200),
            3 => rng.gen_range_usize(200, 1000),
            4 => rng.gen_range_usize(1000, 5000),
            _ => rng.gen_range_usize(5000, 10000),
        };
        let max_v = match tries % 3 {
            0 => 1_000_000_000i64,
            1 => 1_000_000i64,
            _ => 100i64,
        };
        let k = rng.gen_range_i64(1, max_v);
        let restaurants: Vec<(i64, i64)> = (0..n).map(|_| (rng.gen_range_i64(1, max_v), rng.gen_range_i64(1, max_v))).collect();
        let inp = build_input(&restaurants, k);
        if !seen.insert(inp.clone()) { continue; }
        let ans = Solution::max_lunch_joy(restaurants, k);
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

