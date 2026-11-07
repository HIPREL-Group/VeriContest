use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_people: Vec<i64>, seed_k: i64) -> (result: (Vec<i64>, i64))
    requires
        1 <= seed_people.len() <= 50,
        1 <= seed_k <= 100,
        forall |i: int| 0 <= i < seed_people.len() ==> 0 <= #[trigger] seed_people[i] <= 100,
    ensures
        1 <= result.0.len() <= 50,
        1 <= result.1 <= 100,
        forall |i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 100,
{
    (seed_people, seed_k)
}

} // verus!

use std::io::Write;

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
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

fn build_input(cases: &[(Vec<i64>, i64)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (a, k) in cases {
        s.push_str(&format!("{} {}\n", a.len(), k));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[usize]) -> String {
    let mut s = String::new();
    for ans in answers {
        s.push_str(&format!("{}\n", ans));
    }
    s
}

fn gen_seed(rng: &mut Rng, mode: usize) -> (Vec<i64>, i64) {
    match mode {
        0 => {
            let n = rng.gen_range_usize(1, 50);
            let k = rng.gen_range_i64(1, 100);
            (vec![0i64; n], k)
        }
        1 => {
            let n = rng.gen_range_usize(1, 50);
            let k = rng.gen_range_i64(1, 100);
            let a: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(k, 100)).collect();
            (a, k)
        }
        2 => {
            let n = rng.gen_range_usize(1, 50);
            let k = rng.gen_range_i64(2, 100);
            let a: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, k - 1)).collect();
            (a, k)
        }
        3 => {
            let n = rng.gen_range_usize(2, 50);
            let k = rng.gen_range_i64(1, 100);
            let a: Vec<i64> = (0..n).map(|i| if i % 2 == 0 { k } else { 0 }).collect();
            (a, k)
        }
        4 => {
            let n = rng.gen_range_usize(2, 50);
            let k = rng.gen_range_i64(1, 95);
            let a: Vec<i64> = (0..n).map(|i| if i < n/2 { 0 } else { k + 5 }).collect();
            (a, k)
        }
        5 => {
            let n = rng.gen_range_usize(2, 50);
            let k = rng.gen_range_i64(1, 95);
            let a: Vec<i64> = (0..n).map(|i| if i < n/2 { k + 5 } else { 0 }).collect();
            (a, k)
        }
        6 => {
            let k = rng.gen_range_i64(1, 100);
            let v = match rng.next_u64() % 3 {
                0 => 0i64,
                1 => k,
                _ => {
                    let upper = if k - 1 < 0 { 0 } else { k - 1 };
                    rng.gen_range_i64(0, upper)
                }
            };
            (vec![v], k)
        }
        _ => {
            let n = rng.gen_range_usize(1, 50);
            let k = rng.gen_range_i64(1, 100);
            let a: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(0, 100)).collect();
            (a, k)
        }
    }
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count = 0usize;

    while count < target {
        let t: usize = if count < 20 { 1 }
                       else if count < 80 { rng.gen_range_usize(2, 6) }
                       else if count < 150 { rng.gen_range_usize(3, 15) }
                       else { rng.gen_range_usize(5, 30) };
        let mut cases: Vec<(Vec<i64>, i64)> = Vec::with_capacity(t);
        for sub in 0..t {
            let mode = (count + sub) % 8;
            let (seed_a, seed_k) = gen_seed(&mut rng, mode);
            let (a, k) = generate_test_case(seed_a, seed_k);
            cases.push((a, k));
        }
        let answers: Vec<usize> = cases.iter().map(|(a, k)| Solution::count_people_helped(a.clone(), *k)).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
