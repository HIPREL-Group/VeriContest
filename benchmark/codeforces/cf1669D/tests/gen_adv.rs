use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    chars: &Vec<u8>,
) -> (cells: Vec<i32>)
    requires
        1 <= chars.len() <= 100000,
        forall|k: int| 0 <= k < chars.len() ==> (
            #[trigger] chars[k] == 0u8 || chars[k] == 1u8 || chars[k] == 2u8
        ),
    ensures
        1 <= cells.len() <= 100000,
        forall|k: int| 0 <= k < cells.len() as int ==> (
            #[trigger] cells[k] as int == 0 || cells[k] as int == 1 || cells[k] as int == 2
        ),
{
    let n = chars.len();
    let mut cells: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == chars.len(),
            0 <= i <= n,
            cells.len() == i,
            forall|k: int| 0 <= k < chars.len() ==> (
                #[trigger] chars[k] == 0u8 || chars[k] == 1u8 || chars[k] == 2u8
            ),
            forall|k: int| 0 <= k < i as int ==> (
                #[trigger] cells[k] as int == chars[k] as int
            ),
        decreases n - i,
    {
        let c = chars[i];
        let v: i32 = if c == 0u8 { 0i32 } else if c == 1u8 { 1i32 } else { 2i32 };
        cells.push(v);
        i = i + 1;
    }
    cells
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
        let x = self.next_u64();
        let v = ((x >> 32) ^ x) as u128;
        (lo as i128 + (v % r) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let x = self.next_u64();
        let v = ((x >> 32) ^ x) as usize;
        lo + v % (hi - lo + 1)
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

fn parse_color(b: u8) -> i32 {
    if b == b'W' { 0 } else if b == b'R' { 1 } else { 2 }
}

fn cells_from_str(s: &str) -> Vec<i32> {
    s.bytes().map(parse_color).collect()
}

fn build_input(cases: &[String]) -> String {
    let mut s = format!("{}\n", cases.len());
    for c in cases {
        s.push_str(&format!("{}\n{}\n", c.len(), c));
    }
    s
}

fn build_output(answers: &[bool]) -> String {
    let mut s = String::new();
    for &a in answers { s.push_str(if a { "YES\n" } else { "NO\n" }); }
    s
}

fn make_test(rng: &mut Rng, mode: usize) -> String {
    let chars = ['W', 'R', 'B'];
    match mode {
        0 => {
            let n = rng.gen_range_usize(1, 50);
            (0..n).map(|_| 'W').collect()
        }
        1 => {
            let n = rng.gen_range_usize(1, 50);
            (0..n).map(|_| 'R').collect()
        }
        2 => {
            let n = rng.gen_range_usize(1, 50);
            (0..n).map(|_| 'B').collect()
        }
        3 => {
            let n = 2 * rng.gen_range_usize(1, 25);
            let mut s = String::new();
            for i in 0..n {
                s.push(if i % 2 == 0 { 'R' } else { 'B' });
            }
            s
        }
        4 => {
            let n = 100;
            (0..n).map(|_| chars[rng.gen_range_usize(0, 2)]).collect()
        }
        5 => {
            // RWB pattern
            let n = rng.gen_range_usize(3, 100);
            (0..n).map(|i| {
                match i % 3 {
                    0 => 'R',
                    1 => 'W',
                    _ => 'B',
                }
            }).collect()
        }
        6 => {
            // R only segments
            let n = rng.gen_range_usize(1, 50);
            (0..n).map(|i| if i % 2 == 0 { 'R' } else { 'W' }).collect()
        }
        7 => {
            // Single R or B in W background
            let n = rng.gen_range_usize(2, 50);
            let mut s: Vec<char> = vec!['W'; n];
            let pos = rng.gen_range_usize(0, n - 1);
            s[pos] = if rng.gen_range_i64(0, 1) == 0 { 'R' } else { 'B' };
            s.iter().collect()
        }
        8 => {
            let n = rng.gen_range_usize(1, 100);
            (0..n).map(|_| chars[rng.gen_range_usize(0, 2)]).collect()
        }
        9 => {
            // RB pairs
            let n = rng.gen_range_usize(1, 25) * 2;
            let mut s = String::new();
            let mut r_first = true;
            for i in 0..n {
                if i % 2 == 0 { r_first = rng.gen_range_i64(0, 1) == 0; }
                if r_first {
                    s.push(if i % 2 == 0 { 'R' } else { 'B' });
                } else {
                    s.push(if i % 2 == 0 { 'B' } else { 'R' });
                }
            }
            s
        }
        _ => {
            let n = rng.gen_range_usize(1, 100);
            (0..n).map(|_| chars[rng.gen_range_usize(0, 2)]).collect()
        }
    }
}

fn main() {
    let mut rng = Rng::new(1);
    let modes = 10usize;
    let total = 200usize;

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;
    let mut idx = 0;
    while count < total {
        let t: usize = if count < 10 { 1 } else { rng.gen_range_usize(1, 10) };
        let mut cases: Vec<String> = Vec::new();
        for _ in 0..t {
            let mode = idx % modes;
            idx += 1;
            cases.push(make_test(&mut rng, mode));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<bool> = cases.iter().map(|c| Solution::possible_picture(cells_from_str(c))).collect();
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

