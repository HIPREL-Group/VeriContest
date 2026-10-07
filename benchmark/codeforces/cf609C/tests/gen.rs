use vstd::prelude::*;

verus! {

pub fn generate_test_case(loads: Vec<i64>, mutation_kind: u8) -> (result: Vec<i64>)
    requires
        1 <= loads.len() <= 100000,
        forall|j: int|
            #![trigger loads@[j]]
            0 <= j < loads.len() ==> 0 <= (loads@[j] as int) <= 20000,
    ensures
        1 <= result.len() <= 100000,
        forall|j: int|
            #![trigger result@[j]]
            0 <= j < result.len() ==> 0 <= (result@[j] as int) <= 20000,
{
    if mutation_kind == 0 {
        // identity
        loads
    } else if mutation_kind == 1 {
        // set first element to 0
        let mut d = loads;
        d.set(0, 0i64);
        d
    } else if mutation_kind == 2 {
        // set first element to 20000
        let mut d = loads;
        d.set(0, 20000i64);
        d
    } else if mutation_kind == 3 && loads.len() >= 2 {
        // swap first two elements
        let mut d = loads;
        let tmp = d[0];
        d.set(0, d[1]);
        d.set(1, tmp);
        d
    } else if mutation_kind == 4 {
        // set all elements to 0
        let mut d = loads;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == loads.len(),
                1 <= d.len() <= 100000,
                forall|j: int| 0 <= j < i ==> d[j] == 0i64,
                forall|j: int| #![trigger d@[j]] i <= j < d.len() ==> 0 <= (d@[j] as int) <= 20000,
            decreases d.len() - i,
        {
            d.set(i, 0i64);
            i += 1;
        }
        d
    } else if mutation_kind == 5 {
        // set all elements to the same value (first element)
        let val = loads[0];
        let mut d = loads;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == loads.len(),
                1 <= d.len() <= 100000,
                0 <= (val as int) <= 20000,
                forall|j: int| #![trigger d@[j]] 0 <= j < i ==> d@[j] == val,
                forall|j: int| #![trigger d@[j]] i <= j < d.len() ==> 0 <= (d@[j] as int) <= 20000,
            decreases d.len() - i,
        {
            d.set(i, val);
            i += 1;
        }
        d
    } else if mutation_kind == 6 && loads.len() < 100000 {
        // grow by one element (push 0)
        let mut d = loads;
        d.push(0i64);
        d
    } else if mutation_kind == 7 && loads.len() > 1 {
        // shrink by one element (pop)
        let mut d = loads;
        d.pop();
        d
    } else if mutation_kind == 8 {
        // set last element to 0
        let mut d = loads;
        let last = d.len() - 1;
        d.set(last, 0i64);
        d
    } else if mutation_kind == 9 {
        // set last element to 20000
        let mut d = loads;
        let last = d.len() - 1;
        d.set(last, 20000i64);
        d
    } else {
        // fallback: identity
        loads
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

fn build_input(loads: &[i64]) -> String {
    let mut s = format!("{}\n", loads.len());
    let parts: Vec<String> = loads.iter().map(|v| v.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(ans: i64) -> String { format!("{}\n", ans) }

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(609);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |a: Vec<i64>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if a.is_empty() || a.len() > 100_000 { return; }
        for &v in &a { if v < 0 || v > 20_000 { return; } }
        let key = format!("{:?}", a);
        if !seen.insert(key) { return; }
        let inp = build_input(&a);
        let ans = Solution::min_balance_seconds(&a);
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    emit(vec![1, 6], &mut seen, &mut out, &mut count);
    emit(vec![10, 11, 10, 11, 10, 11, 11], &mut seen, &mut out, &mut count);
    emit(vec![1, 2, 3, 4, 5], &mut seen, &mut out, &mut count);
    emit(vec![0], &mut seen, &mut out, &mut count);
    emit(vec![20_000], &mut seen, &mut out, &mut count);
    emit(vec![0, 0], &mut seen, &mut out, &mut count);
    emit(vec![0, 1], &mut seen, &mut out, &mut count);
    emit(vec![0, 20_000], &mut seen, &mut out, &mut count);
    emit(vec![20_000, 0], &mut seen, &mut out, &mut count);
    emit(vec![5; 100], &mut seen, &mut out, &mut count);
    emit(vec![0; 50], &mut seen, &mut out, &mut count);
    emit(vec![20_000; 30], &mut seen, &mut out, &mut count);

    while count < target {
        let n = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(2, 50),
            2 => rng.gen_range_usize(50, 500),
            _ => rng.gen_range_usize(500, 2000),
        };
        let max_v: i64 = match rng.gen_range_usize(0, 4) {
            0 => 5,
            1 => 100,
            2 => 1000,
            _ => 20_000,
        };
        let a: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(0, max_v)).collect();
        emit(a, &mut seen, &mut out, &mut count);
    }
}

