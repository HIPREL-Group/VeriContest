use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    final_d: i32,
    moves: Vec<i32>,
) -> (res: (i32, Vec<i32>))
    requires
        0 <= final_d <= 9,
        moves.len() <= 10,
        forall|j: int| 0 <= j < moves.len() ==> #[trigger] moves[j] == 1 || moves[j] == -1,
    ensures
        0 <= res.0 <= 9,
        res.1.len() == moves.len(),
        res.1.len() <= 10,
        res.0 == final_d,
        forall|j: int| 0 <= j < res.1.len() ==> #[trigger] res.1[j] == 1 || res.1[j] == -1,
{
    (final_d, moves)
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

type TC = (usize, Vec<i32>, Vec<String>);

fn build_input(cases: &[TC]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (n, a, moves) in cases {
        s.push_str(&format!("{}\n", n));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
        for m in moves {
            s.push_str(&format!("{} {}\n", m.len(), m));
        }
    }
    s
}

fn build_output(cases: &[TC]) -> String {
    let mut s = String::new();
    for (n, a, moves) in cases {
        let mut parts: Vec<String> = Vec::with_capacity(*n);
        for i in 0..*n {
            let mvs: Vec<i32> = moves[i].as_bytes().iter().map(|&b| if b == b'U' { 1i32 } else { -1i32 }).collect();
            let init = Solution::recover_digit(a[i], mvs);
            parts.push(init.to_string());
        }
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn random_case(rng: &mut Rng, max_n: usize, mode: usize) -> TC {
    let n = match mode {
        0 => 1,
        1 => rng.gen_range_usize(1, 5),
        2 => rng.gen_range_usize(50, 100),
        _ => rng.gen_range_usize(1, max_n),
    };
    let a: Vec<i32> = (0..n).map(|_| {
        match mode {
            3 => 0,
            4 => 9,
            _ => rng.gen_range_i32(0, 9),
        }
    }).collect();
    let moves: Vec<String> = (0..n).map(|_| {
        let len = match mode {
            5 => 10,  // max length
            6 => 1,
            _ => rng.gen_range_usize(1, 10),
        };
        let mut s = String::with_capacity(len);
        for _ in 0..len {
            let c = match mode {
                7 => 'U',
                8 => 'D',
                _ => if rng.next_u64() % 2 == 0 { 'U' } else { 'D' },
            };
            s.push(c);
        }
        s
    }).collect();
    (n, a, moves)
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1703);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut tries = 0usize;

    while count < target && tries < 100000 {
        tries += 1;
        let t: usize = if count % 4 == 0 { rng.gen_range_usize(2, 20) } else { 1 };
        let mut cases: Vec<TC> = Vec::new();
        for _ in 0..t {
            let mode = (rng.next_u64() as usize) % 9;
            let max_n = if mode == 2 { 100 } else { 50 };
            cases.push(random_case(&mut rng, max_n, mode));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

