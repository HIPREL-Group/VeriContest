use vstd::prelude::*;

verus! {

pub open spec fn is_color(c: int) -> bool {
    c == 0 || c == 1 || c == 2
}

pub fn generate_test_case(cells: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= cells.len() <= 100000,
        forall|k: int| 0 <= k < cells.len() as int ==> is_color(#[trigger] cells[k] as int),
    ensures
        1 <= result.len() <= 100000,
        forall|k: int| 0 <= k < result.len() as int ==> is_color(#[trigger] result[k] as int),
{
    if mutation_kind == 0 {
        // identity
        cells
    } else if mutation_kind == 1 {
        // set first element to 0 (white)
        let mut d = cells;
        d.set(0, 0);
        d
    } else if mutation_kind == 2 {
        // set first element to 1 (red)
        let mut d = cells;
        d.set(0, 1);
        d
    } else if mutation_kind == 3 {
        // set first element to 2 (blue)
        let mut d = cells;
        d.set(0, 2);
        d
    } else if mutation_kind == 4 {
        // set last element to 0 (white)
        let mut d = cells;
        let last = d.len() - 1;
        d.set(last, 0);
        d
    } else if mutation_kind == 5 {
        // set last element to 1 (red)
        let mut d = cells;
        let last = d.len() - 1;
        d.set(last, 1);
        d
    } else if mutation_kind == 6 {
        // set last element to 2 (blue)
        let mut d = cells;
        let last = d.len() - 1;
        d.set(last, 2);
        d
    } else if mutation_kind == 7 {
        // set all elements to 0 (all white)
        let mut d = cells;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == cells.len(),
                1 <= d.len() <= 100000,
                forall|j: int| 0 <= j < i ==> d[j] == 0i32,
                forall|j: int| i <= j < d.len() as int ==> d[j] == cells[j],
            decreases d.len() - i,
        {
            d.set(i, 0);
            i += 1;
        }
        d
    } else if mutation_kind == 8 {
        // set all elements to 1 (all red)
        let mut d = cells;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == cells.len(),
                1 <= d.len() <= 100000,
                forall|j: int| 0 <= j < i ==> d[j] == 1i32,
                forall|j: int| i <= j < d.len() as int ==> d[j] == cells[j],
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        d
    } else if mutation_kind == 9 {
        // set all elements to 2 (all blue)
        let mut d = cells;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == cells.len(),
                1 <= d.len() <= 100000,
                forall|j: int| 0 <= j < i ==> d[j] == 2i32,
                forall|j: int| i <= j < d.len() as int ==> d[j] == cells[j],
            decreases d.len() - i,
        {
            d.set(i, 2);
            i += 1;
        }
        d
    } else if mutation_kind == 10 && cells.len() < 100000 {
        // grow by one element (push 0)
        let mut d = cells;
        d.push(0);
        d
    } else if mutation_kind == 11 && cells.len() > 1 {
        // shrink by one element (pop)
        let mut d = cells;
        d.pop();
        d
    } else {
        cells // fallback
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

fn random_string(rng: &mut Rng, n: usize) -> String {
    let chars = ['W', 'R', 'B'];
    (0..n).map(|_| chars[rng.gen_range_usize(0, 2)]).collect()
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut seen: HashSet<String> = HashSet::new();

    let emit = |cases: &[String], seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let inp = build_input(cases);
        if !seen.insert(inp.clone()) { return; }
        let answers: Vec<bool> = cases.iter().map(|c| Solution::possible_picture(cells_from_str(c))).collect();
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    let exs: Vec<String> = vec![
        "WRBWBR".to_string(),
        "RWBR".to_string(),
        "BRBR".to_string(),
        "RB".to_string(),
        "BR".to_string(),
        "WWW".to_string(),
        "R".to_string(),
        "B".to_string(),
        "W".to_string(),
    ];
    emit(&exs, &mut seen, &mut out, &mut count);
    for ex in &exs { emit(&[ex.clone()], &mut seen, &mut out, &mut count); }

    while count < target {
        let t: usize = if count < 5 { 1 } else { rng.gen_range_usize(1, 30) };
        let mut cases: Vec<String> = Vec::new();
        for _ in 0..t {
            let n = rng.gen_range_usize(1, 30);
            cases.push(random_string(&mut rng, n));
        }
        emit(&cases, &mut seen, &mut out, &mut count);
    }
}

