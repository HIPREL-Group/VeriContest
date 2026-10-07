use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: usize, fillers_s: &Vec<u8>, fillers_f: &Vec<u8>, mutation_kind: u8) -> (result: (Vec<u8>, Vec<u8>))
    requires
        1 <= seed_n <= 50,
        fillers_s.len() == seed_n,
        fillers_f.len() == seed_n,
        forall |i: int| 0 <= i < fillers_s.len() ==> #[trigger] fillers_s[i] <= 1,
        forall |i: int| 0 <= i < fillers_f.len() ==> #[trigger] fillers_f[i] <= 1,
    ensures
        1 <= result.0.len() <= 100_000,
        result.0.len() == result.1.len(),
        forall |i: int| 0 <= i < result.0.len() ==> #[trigger] result.0[i] <= 1,
        forall |i: int| 0 <= i < result.1.len() ==> #[trigger] result.1[i] <= 1,
{
    let mut s: Vec<u8> = Vec::new();
    let mut f: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < seed_n
        invariant
            seed_n == fillers_s.len(),
            seed_n == fillers_f.len(),
            1 <= seed_n <= 50,
            0 <= i <= seed_n,
            s.len() == i,
            f.len() == i,
            forall |j: int| 0 <= j < fillers_s.len() ==> #[trigger] fillers_s[j] <= 1,
            forall |j: int| 0 <= j < fillers_f.len() ==> #[trigger] fillers_f[j] <= 1,
            forall |j: int| 0 <= j < s.len() ==> #[trigger] s[j] <= 1,
            forall |j: int| 0 <= j < f.len() ==> #[trigger] f[j] <= 1,
        decreases seed_n - i,
    {
        if mutation_kind == 0 {
            s.push(fillers_s[i]);
            f.push(fillers_f[i]);
        } else if mutation_kind == 1 {
            s.push(0);
            f.push(0);
        } else if mutation_kind == 2 {
            s.push(1);
            f.push(1);
        } else if mutation_kind == 3 {
            s.push(fillers_s[i]);
            f.push(0);
        } else if mutation_kind == 4 {
            s.push(0);
            f.push(fillers_f[i]);
        } else if mutation_kind == 5 {
            s.push(1);
            f.push(0);
        } else {
            s.push(0);
            f.push(1);
        }
        i = i + 1;
    }
    (s, f)
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

fn vec_to_str(v: &Vec<u8>) -> String {
    let mut s = String::with_capacity(v.len());
    for x in v {
        if *x == 1 { s.push('1'); } else { s.push('0'); }
    }
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1921);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f_out = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f_out);
    let mut count = 0usize;
    let mut seen = HashSet::new();

    while count < target {
        let t = if count < 5 { 1usize } else { rng.gen_range_usize(1, 5) };
        let mut input = format!("{}\n", t);
        let mut output = String::new();
        for _ in 0..t {
            let n = rng.gen_range_usize(1, 50);
            let mut fs: Vec<u8> = Vec::with_capacity(n);
            let mut ff: Vec<u8> = Vec::with_capacity(n);
            for _ in 0..n {
                fs.push((rng.next_u64() & 1) as u8);
                ff.push((rng.next_u64() & 1) as u8);
            }
            let mk = (rng.next_u64() % 7) as u8;
            let (sv, fv) = generate_test_case(n, &fs, &ff, mk);
            input.push_str(&format!("{}\n{}\n{}\n", sv.len(), vec_to_str(&sv), vec_to_str(&fv)));
            let ans = Solution::min_days(sv, fv);
            output.push_str(&format!("{}\n", ans));
        }
        if !seen.insert(input.clone()) { continue; }
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&input), fmt_json_str(&output)).unwrap();
        count += 1;
    }
}
