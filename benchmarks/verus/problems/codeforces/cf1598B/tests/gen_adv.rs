use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    d1: usize,
    d2: usize,
    half1_count: usize,
    extras: &Vec<u8>,
) -> (result: (usize, Vec<Vec<bool>>))
    requires
        2 <= n <= 1000,
        n % 2 == 0,
        d1 < 5,
        d2 < 5,
        d1 != d2,
        half1_count == n / 2,
        extras.len() == n,
        forall|i: int| 0 <= i < extras.len() ==> extras[i] < 32,
    ensures
        result.0 == n,
        result.1.len() == n,
        forall|i: int| 0 <= i && i < n ==> (#[trigger] result.1@[i]).len() == 5,
        forall|i: int| 0 <= i && i < n ==>
            result.1@[i]@[0] || result.1@[i]@[1] || result.1@[i]@[2] || result.1@[i]@[3] || result.1@[i]@[4],
{
    let mut days: Vec<Vec<bool>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            days.len() == i,
            d1 < 5,
            d2 < 5,
            d1 != d2,
            half1_count == n / 2,
            extras.len() == n,
            forall|k: int| 0 <= k < i ==> (#[trigger] days@[k]).len() == 5,
            forall|k: int| 0 <= k < i ==>
                days@[k]@[0] || days@[k]@[1] || days@[k]@[2] || days@[k]@[3] || days@[k]@[4],
        decreases n - i,
    {
        let mut row: Vec<bool> = Vec::new();
        row.push(false);
        row.push(false);
        row.push(false);
        row.push(false);
        row.push(false);

        // Determine primary day
        let primary: usize = if i < half1_count { d1 } else { d2 };
        row.set(primary, true);

        // Add extra days based on extras[i], but ensure primary stays true
        let e = extras[i];
        let mut j: usize = 0;
        while j < 5
            invariant
                j <= 5,
                row.len() == 5,
                primary < 5,
                row@[primary as int] == true,
            decreases 5 - j,
        {
            let bit: u8 = 1u8 << (j as u8);
            if (e & bit) != 0 && j != primary {
                row.set(j, true);
            }
            j = j + 1;
        }

        assert(row@[primary as int] == true);
        assert(primary < 5);
        assert(row@[0] || row@[1] || row@[2] || row@[3] || row@[4]) by {
            if primary == 0 { assert(row@[0]); }
            else if primary == 1 { assert(row@[1]); }
            else if primary == 2 { assert(row@[2]); }
            else if primary == 3 { assert(row@[3]); }
            else { assert(row@[4]); }
        };

        days.push(row);
        i = i + 1;
    }

    (n, days)
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

fn build_input(cases: &[Vec<Vec<bool>>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for days in cases {
        s.push_str(&format!("{}\n", days.len()));
        for row in days {
            let parts: Vec<String> = row.iter().map(|v| if *v { "1".to_string() } else { "0".to_string() }).collect();
            s.push_str(&parts.join(" "));
            s.push('\n');
        }
    }
    s
}

fn build_output(answers: &[bool]) -> String {
    let mut s = String::new();
    for &a in answers { s.push_str(if a { "YES\n" } else { "NO\n" }); }
    s
}

fn random_row(rng: &mut Rng) -> Vec<bool> {
    loop {
        let row: Vec<bool> = (0..5).map(|_| rng.gen_range_i64(0, 1) == 1).collect();
        if row.iter().any(|&x| x) { return row; }
    }
}

fn make_test(rng: &mut Rng, mode: usize) -> Vec<Vec<bool>> {
    match mode {
        0 => {
            let mut v = Vec::new();
            v.push(vec![true, false, false, false, false]);
            v.push(vec![true, false, false, false, false]);
            v
        }
        1 => {
            let n = rng.gen_range_usize(1, 50) * 2;
            (0..n).map(|_| random_row(rng)).collect()
        }
        2 => {
            // All same single day
            let n = rng.gen_range_usize(1, 50) * 2;
            let day = rng.gen_range_usize(0, 4);
            (0..n).map(|_| {
                let mut row = vec![false; 5];
                row[day] = true;
                row
            }).collect()
        }
        3 => {
            // All days enabled
            let n = rng.gen_range_usize(1, 50) * 2;
            (0..n).map(|_| vec![true; 5]).collect()
        }
        4 => {
            // Two halves with single days
            let n = rng.gen_range_usize(1, 50) * 2;
            let half = n / 2;
            let mut v = Vec::new();
            for _ in 0..half {
                let mut row = vec![false; 5];
                row[0] = true;
                v.push(row);
            }
            for _ in half..n {
                let mut row = vec![false; 5];
                row[1] = true;
                v.push(row);
            }
            v
        }
        5 => {
            // Imbalanced: one day has too few
            let n = rng.gen_range_usize(2, 50) * 2;
            let mut v = Vec::new();
            for i in 0..n {
                let mut row = vec![false; 5];
                if i < 2 { row[0] = true; row[1] = true; }
                else { row[1] = true; }
                v.push(row);
            }
            v
        }
        6 => {
            // Two adjacent days only
            let n = rng.gen_range_usize(1, 30) * 2;
            (0..n).map(|_| {
                let mut row = vec![false; 5];
                row[2] = rng.gen_range_i64(0, 1) == 1;
                row[3] = rng.gen_range_i64(0, 1) == 1;
                if !row[2] && !row[3] { row[2] = true; }
                row
            }).collect()
        }
        7 => {
            // Large n
            let n = 200;
            (0..n).map(|_| random_row(rng)).collect()
        }
        8 => {
            let n = rng.gen_range_usize(1, 30) * 2;
            (0..n).map(|_| {
                let nb = rng.gen_range_usize(1, 5);
                let mut row = vec![false; 5];
                let mut cnt = 0;
                while cnt < nb {
                    let d = rng.gen_range_usize(0, 4);
                    if !row[d] { row[d] = true; cnt += 1; }
                }
                row
            }).collect()
        }
        9 => {
            let n = 1000;
            (0..n).map(|_| random_row(rng)).collect()
        }
        _ => {
            let n = rng.gen_range_usize(1, 50) * 2;
            (0..n).map(|_| random_row(rng)).collect()
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
    let mut idx = 0usize;
    while count < total {
        let t: usize = if count < 10 { 1 } else { rng.gen_range_usize(1, 5) };
        let mut cases: Vec<Vec<Vec<bool>>> = Vec::new();
        for _ in 0..t {
            let mode = idx % modes;
            idx += 1;
            cases.push(make_test(&mut rng, mode));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<bool> = cases.iter().map(|days| Solution::groups(days.len(), days.clone())).collect();
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

