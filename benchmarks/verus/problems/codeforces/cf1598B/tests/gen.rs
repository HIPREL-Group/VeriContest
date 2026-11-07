use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n_half: usize,
    base_day: Vec<u8>,
    mutation_kind: u8,
) -> (result: (usize, Vec<Vec<bool>>))
    requires
        1 <= n_half <= 500,
        base_day.len() == 2 * n_half,
        forall|i: int| 0 <= i < base_day.len() ==> 0 <= #[trigger] base_day[i] <= 4,
    ensures
        2 <= result.0 && result.0 <= 1000,
        result.0 % 2 == 0,
        result.1.len() == result.0,
        forall|i: int| 0 <= i && i < result.0 ==> result.1@[i].len() == 5,
        forall|i: int| 0 <= i && i < result.0 ==>
            result.1@[i]@[0] || result.1@[i]@[1] || result.1@[i]@[2] || result.1@[i]@[3] || result.1@[i]@[4],
{
    let n: usize = 2 * n_half;
    let mut days: Vec<Vec<bool>> = Vec::new();
    let mut idx: usize = 0;

    while idx < n
        invariant
            n == 2 * n_half,
            1 <= n_half <= 500,
            2 <= n <= 1000,
            n % 2 == 0,
            days.len() == idx,
            idx <= n,
            base_day.len() == n,
            forall|k: int| 0 <= k < base_day.len() ==> 0 <= #[trigger] base_day[k] <= 4,
            forall|j: int| 0 <= j < idx as int ==> (#[trigger] days@[j]).len() == 5,
            forall|j: int| 0 <= j < idx as int ==>
                days@[j]@[0] || days@[j]@[1] || days@[j]@[2] || days@[j]@[3] || days@[j]@[4],
        decreases n - idx,
    {
        let bd = base_day[idx];

        let mut d0: bool = bd == 0u8;
        let mut d1: bool = bd == 1u8;
        let mut d2: bool = bd == 2u8;
        let mut d3: bool = bd == 3u8;
        let mut d4: bool = bd == 4u8;

        if mutation_kind == 1 {
            d0 = true; d1 = true; d2 = true; d3 = true; d4 = true;
        } else if mutation_kind == 2 {
            d0 = true;
        } else if mutation_kind == 3 {
            d4 = true;
        } else if mutation_kind == 4 {
            d0 = true; d1 = false; d2 = false; d3 = false; d4 = false;
        } else if mutation_kind == 5 {
            d0 = false; d1 = false; d2 = false; d3 = false; d4 = true;
        }

        proof {
            assert(bd == 0u8 || bd == 1u8 || bd == 2u8 || bd == 3u8 || bd == 4u8);
        }
        assert(d0 || d1 || d2 || d3 || d4);

        let mut row: Vec<bool> = Vec::new();
        row.push(d0);
        row.push(d1);
        row.push(d2);
        row.push(d3);
        row.push(d4);

        assert(row.len() == 5);
        assert(row@[0] == d0);
        assert(row@[1] == d1);
        assert(row@[2] == d2);
        assert(row@[3] == d3);
        assert(row@[4] == d4);
        assert(row@[0] || row@[1] || row@[2] || row@[3] || row@[4]);

        days.push(row);
        idx += 1;
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

fn random_days(rng: &mut Rng, n: usize) -> Vec<Vec<bool>> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        loop {
            let row: Vec<bool> = (0..5).map(|_| rng.gen_range_i64(0, 1) == 1).collect();
            if row.iter().any(|&x| x) {
                v.push(row);
                break;
            }
        }
    }
    v
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut seen: HashSet<String> = HashSet::new();

    let emit = |cases: &[Vec<Vec<bool>>], seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let inp = build_input(cases);
        if !seen.insert(inp.clone()) { return; }
        let answers: Vec<bool> = cases.iter().map(|days| Solution::groups(days.len(), days.clone())).collect();
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // Examples
    let ex1: Vec<Vec<bool>> = vec![
        vec![true, false, false, true, false],
        vec![false, true, false, false, true],
        vec![false, false, false, true, false],
        vec![false, true, false, true, false],
    ];
    let ex2: Vec<Vec<bool>> = vec![
        vec![false, false, false, true, false],
        vec![false, false, false, true, false],
    ];
    emit(&[ex1.clone(), ex2.clone()], &mut seen, &mut out, &mut count);
    emit(&[ex1.clone()], &mut seen, &mut out, &mut count);
    emit(&[ex2.clone()], &mut seen, &mut out, &mut count);

    while count < target {
        let t: usize = if count < 5 { 1 } else { rng.gen_range_usize(1, 20) };
        let mut cases: Vec<Vec<Vec<bool>>> = Vec::new();
        for _ in 0..t {
            let n = rng.gen_range_usize(1, 25) * 2;
            let days = random_days(&mut rng, n);
            cases.push(days);
        }
        emit(&cases, &mut seen, &mut out, &mut count);
    }
}

