use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: usize, seed_k: i64, fillers: &Vec<i64>, mutation_kind: u8) -> (result: (Vec<i64>, i64))
    requires
        1 <= seed_n <= 50,
        fillers.len() == seed_n,
        1 <= seed_k <= 100,
        forall |i: int| 0 <= i < fillers.len() ==> 0 <= #[trigger] fillers[i] <= 100,
    ensures
        1 <= result.0.len() <= 50,
        1 <= result.1 <= 100,
        forall |i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 100,
{
    let mut people: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < seed_n
        invariant
            seed_n == fillers.len(),
            1 <= seed_n <= 50,
            0 <= i <= seed_n,
            people.len() == i,
            forall |j: int| 0 <= j < fillers.len() ==> 0 <= #[trigger] fillers[j] <= 100,
            forall |j: int| 0 <= j < i as int ==> people[j] == fillers[j],
            forall |j: int| 0 <= j < people.len() ==> 0 <= #[trigger] people[j] <= 100,
        decreases seed_n - i,
    {
        people.push(fillers[i]);
        i = i + 1;
    }
    let _ = mutation_kind;
    (people, seed_k)
}

} // verus!

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

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);
    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut seen = HashSet::new();
    
    while count < target {
        let t = if count < 5 { 1usize } else { rng.gen_range_usize(1, 30) };
        let mut input = format!("{}\n", t);
        let mut output = String::new();
        for _ in 0..t {
            let n = rng.gen_range_usize(1, 50);
            let k = rng.gen_range_i64(1, 100);
            let mut fillers: Vec<i64> = Vec::with_capacity(n);
            for _ in 0..n {
                fillers.push(rng.gen_range_i64(0, 100));
            }
            let mk = (rng.next_u64() % 8) as u8;
            let (people, kk) = generate_test_case(n, k, &fillers, mk);
            input.push_str(&format!("{} {}\n", people.len(), kk));
            let parts: Vec<String> = people.iter().map(|x| x.to_string()).collect();
            input.push_str(&parts.join(" "));
            input.push('\n');
            let ans = Solution::count_people_helped(people, kk);
            output.push_str(&format!("{}\n", ans));
        }
        let key = input.clone();
        if !seen.insert(key) { continue; }
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&input), fmt_json_str(&output)).unwrap();
        count += 1;
    }
}
