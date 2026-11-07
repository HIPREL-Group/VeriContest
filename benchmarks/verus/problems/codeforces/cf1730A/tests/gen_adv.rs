use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    c_val: i32,
    vals: &Vec<i32>,
) -> (res: (Vec<i32>, i32))
    requires
        1 <= n <= 100,
        1 <= c_val <= 100,
        vals.len() == n,
        forall|i: int| 0 <= i < vals.len() ==> 1 <= #[trigger] vals[i] <= 100,
    ensures
        1 <= res.0.len() <= 100,
        1 <= res.1 <= 100,
        forall|i: int| 0 <= i < res.0.len() ==> 1 <= #[trigger] res.0@[i] <= 100,
{
    let mut out: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == vals.len(),
            1 <= n <= 100,
            out.len() == i,
            forall|k: int| 0 <= k < out.len() ==> 1 <= #[trigger] out[k] <= 100,
            forall|k: int| 0 <= k < vals.len() ==> 1 <= #[trigger] vals[k] <= 100,
        decreases n - i,
    {
        out.push(vals[i]);
        i = i + 1;
    }
    (out, c_val)
}

}

use std::io::Write;
use std::collections::HashSet;

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self { Self(seed.wrapping_add(1)) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let r = (hi as i64 - lo as i64 + 1) as u64;
        (lo as i64 + (self.next_u64() % r) as i64) as i32
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

type TC = (usize, i32, Vec<i32>);

fn build_input(cases: &[TC]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (n, c, orbits) in cases {
        s.push_str(&format!("{} {}\n", n, c));
        let parts: Vec<String> = orbits.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(cases: &[TC]) -> String {
    let mut s = String::new();
    for (_n, c, orbits) in cases {
        let ans = Solution::min_destroy_cost(orbits.clone(), *c);
        s.push_str(&format!("{}\n", ans));
    }
    s
}

fn gen_case(rng: &mut Rng, mode: usize) -> TC {
    match mode {
        0 => {
            // n=1
            let c = rng.gen_range_i32(1, 100);
            let orb = rng.gen_range_i32(1, 100);
            (1, c, vec![orb])
        }
        1 => {
            // c=1 (always cheap to use machine 1)
            let n = rng.gen_range_usize(1, 100);
            let orbits: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(1, 100)).collect();
            (n, 1, orbits)
        }
        2 => {
            // c=100 (machine 1 is cheaper unless many on same orbit)
            let n = rng.gen_range_usize(1, 100);
            let orbits: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(1, 100)).collect();
            (n, 100, orbits)
        }
        3 => {
            // all on same orbit
            let n = rng.gen_range_usize(1, 100);
            let c = rng.gen_range_i32(1, 100);
            let orb = rng.gen_range_i32(1, 100);
            (n, c, vec![orb; n])
        }
        4 => {
            // all distinct orbits
            let n = rng.gen_range_usize(1, 100);
            let c = rng.gen_range_i32(1, 100);
            let mut orbs: Vec<i32> = (1..=100i32).collect();
            // Randomize and pick first n
            for i in (1..orbs.len()).rev() {
                let j = rng.gen_range_usize(0, i);
                orbs.swap(i, j);
            }
            let mut sel = Vec::with_capacity(n);
            for i in 0..n {
                sel.push(orbs[i % 100]);
            }
            (n, c, sel)
        }
        _ => {
            let n = rng.gen_range_usize(1, 100);
            let c = rng.gen_range_i32(1, 100);
            let orbits: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(1, 100)).collect();
            (n, c, orbits)
        }
    }
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1730);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut tries = 0usize;

    while count < target && tries < 100000 {
        tries += 1;
        let t: usize = if count % 5 == 0 { rng.gen_range_usize(2, 30) } else { 1 };
        let mut cases: Vec<TC> = Vec::new();
        for _ in 0..t {
            let mode = (rng.next_u64() as usize) % 6;
            cases.push(gen_case(&mut rng, mode));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

