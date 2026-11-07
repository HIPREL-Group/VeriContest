use vstd::prelude::*;

verus! {

pub open spec fn sorted(s: Seq<i64>, n: int) -> bool {
    n <= s.len() && forall|i: int| 0 <= i < n - 1 ==> #[trigger] s[i] <= s[i + 1]
}

pub open spec fn spec_sum_upto(s: Seq<i64>, n: int) -> int
    decreases n,
{
    if n <= 0 { 0 } else { spec_sum_upto(s, n - 1) + s[n - 1] }
}

pub fn input_sum(a: &Vec<i64>) -> (result: i64)
    requires
        1 <= a.len() <= 200000,
        forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 1000000000,
    ensures
        result == spec_sum_upto(a@, a.len() as int),
        a.len() <= result <= a.len() * 1000000000,
{
    let mut i = 0usize;
    let mut sum = 0i64;
    while i < a.len()
        invariant
            1 <= a.len() <= 200000,
            forall|j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j] <= 1000000000,
            0 <= i <= a.len(),
            i <= sum <= i * 1000000000,
            sum == spec_sum_upto(a@, i as int),
        decreases a.len() - i,
    {
        sum += a[i];
        i += 1;
    }
    sum
}

pub fn generate_test_case(raw: Vec<i64>, k: i64) -> (result: (usize, i64, Vec<i64>))
    ensures
        1 <= result.0 <= 200000,
        result.0 == result.2.len(),
        sorted(result.2@, result.0 as int),
        forall|i: int| 0 <= i < result.2.len() ==> 1 <= #[trigger] result.2[i] <= 1000000000,
        1 <= result.1 <= 1000000000,
        result.1 <= spec_sum_upto(result.2@, result.0 as int),
{
    let n = if raw.len() == 0 { 1usize } else if raw.len() > 200000 { 200000usize } else { raw.len() };
    let mut a: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 200000, 0 <= i <= n, a.len() == i,
            forall|j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j] <= 1000000000,
            forall|j: int| 0 <= j < a.len() - 1 ==> #[trigger] a[j] <= a[j + 1],
        decreases n - i,
    {
        let v = if i < raw.len() { raw[i] } else { 1 };
        let mut v = if v < 1 { 1 } else if v > 1000000000 { 1000000000 } else { v };
        if i > 0 && v < a[i - 1] { v = a[i - 1]; }
        a.push(v);
        i += 1;
    }
    let sum = input_sum(&a);
    let k = if k < 1 { 1 } else if k > 1000000000 { 1000000000 } else { k };
    let k = if k > sum { sum } else { k };
    (n, k, a)
}


pub fn generate_candidate(
    seed_n: usize,
    seed_k: i64,
    seed_a: &Vec<i64>,
) -> (res: (usize, i64, Vec<i64>))
    requires
        1 <= seed_n <= 200_000,
        seed_n == seed_a.len(),
        forall|i: int| 0 <= i < seed_a.len() ==>
            1 <= (#[trigger] seed_a[i]) <= 1_000_000_000,
        1 <= seed_k <= 1_000_000_000,
        forall|i: int| 0 <= i < seed_n as int - 1 ==>
            #[trigger] seed_a[i] <= seed_a[i + 1],
    ensures
        1 <= res.0 <= 200_000,
        res.0 == res.2.len(),
        forall|i: int| 0 <= i < res.2.len() ==>
            1 <= (#[trigger] res.2[i]) <= 1_000_000_000,
        1 <= res.1 <= 1_000_000_000,
        forall|i: int| 0 <= i < res.0 as int - 1 ==>
            #[trigger] res.2[i] <= res.2[i + 1],
{
    let n = seed_a.len();
    let mut a: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == seed_a.len(),
            n == seed_n,
            1 <= n <= 200_000,
            0 <= i <= n,
            a.len() == i,
            forall|j: int| 0 <= j < seed_a.len() ==>
                1 <= (#[trigger] seed_a[j]) <= 1_000_000_000,
            forall|j: int| 0 <= j < i as int ==>
                a[j] == seed_a[j],
            forall|j: int| 0 <= j < i as int ==>
                1 <= (#[trigger] a[j]) <= 1_000_000_000,
            forall|j: int| 0 <= j < seed_n as int - 1 ==>
                #[trigger] seed_a[j] <= seed_a[j + 1],
        decreases n - i,
    {
        a.push(seed_a[i]);
        i = i + 1;
    }
    assert(a.len() == n);
    assert forall|j: int| 0 <= j < seed_n as int - 1 implies
        #[trigger] a[j] <= a[j + 1] by {
        if 0 <= j < seed_n as int - 1 {
            assert(a[j] == seed_a[j]);
            assert(a[j + 1] == seed_a[j + 1]);
        }
    };
    (seed_n, seed_k, a)
}

} // verus!

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
    for (a, k) in cases {
        s.push_str(&format!("{} {}\n", a.len(), k));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
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

fn make_seed_case(rng: &mut Rng, mode: usize) -> (Vec<i64>, i64) {
    match mode {
        0 => {
            // n=1
            let v = rng.gen_range_i64(1, 100);
            let kv = if v >= 1 { rng.gen_range_i64(1, v) } else { 1 };
            (vec![v], kv)
        }
        1 => {
            // all equal
            let n = rng.gen_range_usize(2, 30);
            let v = rng.gen_range_i64(1, 100);
            let total = (v * n as i64).min(1_000_000_000);
            (vec![v; n], rng.gen_range_i64(1, total.max(1)))
        }
        2 => {
            // distinct values
            let n = rng.gen_range_usize(2, 20);
            let a: Vec<i64> = (1..=n as i64).collect();
            let total: i64 = a.iter().sum::<i64>().min(1_000_000_000);
            (a, rng.gen_range_i64(1, total.max(1)))
        }
        3 => {
            // big values
            let n = rng.gen_range_usize(1, 30);
            let a: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, 1_000_000_000)).collect();
            (a, rng.gen_range_i64(1, 1_000_000_000))
        }
        4 => {
            // small total
            let n = rng.gen_range_usize(1, 20);
            let a: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, 1000)).collect();
            let total: i64 = a.iter().sum::<i64>().min(1_000_000_000);
            (a, total.max(1))
        }
        5 => {
            // k = 1
            let n = rng.gen_range_usize(1, 20);
            let a: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, 1000)).collect();
            (a, 1)
        }
        _ => {
            let n = rng.gen_range_usize(1, 50);
            let a: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, 1000)).collect();
            let total: i64 = a.iter().sum::<i64>().min(1_000_000_000);
            (a, rng.gen_range_i64(1, total.max(1)))
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
    let modes = 7usize;
    let mut seen: HashSet<String> = HashSet::new();

    while count < target {
        let t: usize = if count < 20 { 1 }
                       else if count < 80 { rng.gen_range_usize(2, 6) }
                       else if count < 150 { rng.gen_range_usize(3, 12) }
                       else { rng.gen_range_usize(5, 25) };
        let mut cases: Vec<(Vec<i64>, i64)> = Vec::new();
        let mut total = 0usize;
        for sub in 0..t {
            let mode = (count + sub) % modes;
            let (mut a, k) = make_seed_case(&mut rng, mode);
            // sort a as required
            a.sort();
            let n = a.len();
            // verify preconditions in verified function
            let (_n2, k2, a2) = generate_candidate(n, k, &a);
            if total + a2.len() > 5000 { break; }
            total += a2.len();
            cases.push((a2, k2));
        }
        if cases.is_empty() { continue; }
        let cases: Vec<_> = cases.iter().map(|c| {
            let (_, k, a) = generate_test_case(c.0.clone(), c.1);
            (a, k)
        }).collect();
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i64> = cases.iter().map(|(a, k)| Solution::min_lemonade_presses(a.len(), *k, a.clone())).collect();
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
