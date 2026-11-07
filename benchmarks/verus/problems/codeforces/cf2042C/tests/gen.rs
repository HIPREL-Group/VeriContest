use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    owners: Vec<i64>,
    k: i64,
    mutation_kind: u8,
) -> (result: (Vec<i64>, i64))
    requires
        2 <= owners.len() <= 200000,
        1 <= k <= 1000000000,
        forall|i: int| 0 <= i < owners.len() ==> #[trigger] owners@[i] == 0 || #[trigger] owners@[i] == 1,
    ensures
        2 <= result.0.len() <= 200000,
        1 <= result.1 <= 1000000000,
        forall|i: int| 0 <= i < result.0.len() ==> #[trigger] result.0@[i] == 0 || #[trigger] result.0@[i] == 1,
{
    if mutation_kind == 0 {
        // identity
        (owners, k)
    } else if mutation_kind == 1 {
        // set first element to 0
        let mut d = owners;
        d.set(0, 0);
        (d, k)
    } else if mutation_kind == 2 {
        // set first element to 1
        let mut d = owners;
        d.set(0, 1);
        (d, k)
    } else if mutation_kind == 3 {
        // set last element to 0
        let mut d = owners;
        let last = d.len() - 1;
        d.set(last, 0);
        (d, k)
    } else if mutation_kind == 4 {
        // set last element to 1
        let mut d = owners;
        let last = d.len() - 1;
        d.set(last, 1);
        (d, k)
    } else if mutation_kind == 5 {
        // set all elements to 0
        let len = owners.len();
        let mut d = owners;
        let mut i: usize = 0;
        while i < len
            invariant
                0 <= i <= len,
                d.len() == len,
                2 <= len <= 200000,
                forall|j: int| 0 <= j < i ==> #[trigger] d@[j] == 0,
                forall|j: int| i <= j < len ==> #[trigger] d@[j] == owners@[j],
            decreases len - i,
        {
            d.set(i, 0);
            i += 1;
        }
        (d, k)
    } else if mutation_kind == 6 {
        // set all elements to 1
        let len = owners.len();
        let mut d = owners;
        let mut i: usize = 0;
        while i < len
            invariant
                0 <= i <= len,
                d.len() == len,
                2 <= len <= 200000,
                forall|j: int| 0 <= j < i ==> #[trigger] d@[j] == 1,
                forall|j: int| i <= j < len ==> #[trigger] d@[j] == owners@[j],
            decreases len - i,
        {
            d.set(i, 1);
            i += 1;
        }
        (d, k)
    } else if mutation_kind == 7 && owners.len() < 200000 {
        // grow by one element (push 0)
        let mut d = owners;
        d.push(0);
        (d, k)
    } else if mutation_kind == 8 && owners.len() < 200000 {
        // grow by one element (push 1)
        let mut d = owners;
        d.push(1);
        (d, k)
    } else if mutation_kind == 9 && owners.len() > 2 {
        // shrink by one element (pop)
        let mut d = owners;
        d.pop();
        (d, k)
    } else if mutation_kind == 10 {
        // flip first element
        let mut d = owners;
        let v = if d[0] == 0 { 1i64 } else { 0i64 };
        d.set(0, v);
        (d, k)
    } else if mutation_kind == 11 {
        // flip last element
        let mut d = owners;
        let last = d.len() - 1;
        let v = if d[last] == 0 { 1i64 } else { 0i64 };
        d.set(last, v);
        (d, k)
    } else if mutation_kind == 12 {
        // k = 1 (min boundary)
        (owners, 1)
    } else if mutation_kind == 13 {
        // k = 1000000000 (max boundary)
        (owners, 1000000000)
    } else if mutation_kind == 14 && k < 1000000000 {
        // nudge k up
        (owners, k + 1)
    } else if mutation_kind == 15 && k > 1 {
        // nudge k down
        (owners, k - 1)
    } else if mutation_kind == 16 && owners.len() >= 2 {
        // swap first two elements
        let mut d = owners;
        let a = d[0];
        let b = d[1];
        d.set(0, b);
        d.set(1, a);
        (d, k)
    } else {
        // fallback: identity
        (owners, k)
    }
}

}

use std::io::Write;
use std::collections::HashSet;

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
    for (owners, k) in cases {
        let n = owners.len();
        s.push_str(&format!("{} {}\n", n, k));
        let mut row = String::with_capacity(n);
        for &v in owners {
            row.push(if v == 1 { '1' } else { '0' });
        }
        row.push('\n');
        s.push_str(&row);
    }
    s
}

fn build_output(answers: &[i64]) -> String {
    let mut s = String::new();
    for ans in answers {
        s.push_str(&format!("{}\n", ans));
    }
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count = 0usize;

    let example: Vec<(Vec<i64>, i64)> = vec![
        (vec![1,0,0,1], 1),
        (vec![1,0,1,0], 1),
        (vec![1,0,1,1], 1),
        (vec![1,0,1,1], 2),
        (vec![0,1,1,1,0,1], 3),
        (vec![0,1,1,1,1,1,1,1,1,1], 2),
        (vec![1,1,1,1,1], 1),
    ];
    {
        let answers: Vec<i64> = example.iter().map(|(o, k)| Solution::minimum_groups(o.clone(), *k)).collect();
        let inp = build_input(&example);
        let outp = build_output(&answers);
        let key = format!("{:?}", example);
        if seen.insert(key) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }

    while count < target {
        let t: usize = if count < 10 { 1 }
                       else if count < 30 { rng.gen_range_usize(2, 5) }
                       else if count < 60 { rng.gen_range_usize(3, 10) }
                       else { rng.gen_range_usize(5, 20) };
        let mut cases: Vec<(Vec<i64>, i64)> = Vec::new();
        let mut total_n = 0usize;
        for _ in 0..t {
            let n = rng.gen_range_usize(2, 50);
            let owners: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(0, 1)).collect();
            let k = rng.gen_range_i64(1, (n as i64).pow(2));
            if total_n + n > 5000 { break; }
            total_n += n;
            cases.push((owners, k));
        }
        if cases.is_empty() { continue; }
        let key = format!("{:?}", cases);
        if !seen.insert(key) { continue; }
        let answers: Vec<i64> = cases.iter().map(|(o, k)| Solution::minimum_groups(o.clone(), *k)).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

