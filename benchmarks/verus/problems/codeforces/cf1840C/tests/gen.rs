use vstd::prelude::*;

verus! {

pub fn generate_test_case(arr: Vec<i64>, k_val: usize, q_val: i64, mutation_kind: u8) -> (result: (usize, usize, i64, Vec<i64>))
    requires
        1 <= arr.len() && arr.len() <= 200000,
        1 <= k_val && k_val <= arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> -1000000000 <= #[trigger] arr[i] && arr[i] <= 1000000000,
    ensures
        1 <= result.0 && result.0 <= 200000,
        1 <= result.1 && result.1 <= result.0,
        result.3.len() == result.0,
        forall|i: int| 0 <= i && i < result.0 ==> -1000000000 <= #[trigger] result.3@[i] && result.3@[i] <= 1000000000,
{
    if mutation_kind == 0 {
        // identity
        let n = arr.len();
        (n, k_val, q_val, arr)
    } else if mutation_kind == 1 {
        // set first element to -1000000000
        let mut d = arr;
        d.set(0, -1000000000i64);
        let n = d.len();
        (n, k_val, q_val, d)
    } else if mutation_kind == 2 {
        // set first element to 1000000000
        let mut d = arr;
        d.set(0, 1000000000i64);
        let n = d.len();
        (n, k_val, q_val, d)
    } else if mutation_kind == 3 {
        // set first element to 0
        let mut d = arr;
        d.set(0, 0i64);
        let n = d.len();
        (n, k_val, q_val, d)
    } else if mutation_kind == 4 {
        // set all elements to 0
        let mut d = arr;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == arr.len(),
                1 <= d.len() && d.len() <= 200000,
                1 <= k_val && k_val <= d.len(),
                forall|j: int| 0 <= j < i ==> d[j] == 0i64,
                forall|j: int| i <= j < d.len() as int ==> d[j] == arr[j],
            decreases d.len() - i,
        {
            d.set(i, 0i64);
            i += 1;
        }
        let n = d.len();
        (n, k_val, q_val, d)
    } else if mutation_kind == 5 {
        // set all elements to 1000000000
        let mut d = arr;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == arr.len(),
                1 <= d.len() && d.len() <= 200000,
                1 <= k_val && k_val <= d.len(),
                forall|j: int| 0 <= j < i ==> d[j] == 1000000000i64,
                forall|j: int| i <= j < d.len() as int ==> d[j] == arr[j],
            decreases d.len() - i,
        {
            d.set(i, 1000000000i64);
            i += 1;
        }
        let n = d.len();
        (n, k_val, q_val, d)
    } else if mutation_kind == 6 && arr.len() + 1 <= 200000 {
        // grow by 1 element
        let mut d = arr;
        d.push(0i64);
        let n = d.len();
        (n, k_val, q_val, d)
    } else if mutation_kind == 7 && arr.len() > 1 && k_val < arr.len() {
        // shrink by 1 element
        let mut d = arr;
        d.pop();
        let n = d.len();
        (n, k_val, q_val, d)
    } else if mutation_kind == 8 && arr[0] < 1000000000i64 {
        // nudge first element up
        let mut d = arr;
        d.set(0, d[0] + 1i64);
        let n = d.len();
        (n, k_val, q_val, d)
    } else if mutation_kind == 9 && arr[0] > -1000000000i64 {
        // nudge first element down
        let mut d = arr;
        d.set(0, d[0] - 1i64);
        let n = d.len();
        (n, k_val, q_val, d)
    } else if mutation_kind == 10 && arr.len() >= 2 {
        // swap first two elements
        let mut d = arr;
        let tmp = d[0];
        d.set(0, d[1]);
        d.set(1, tmp);
        let n = d.len();
        (n, k_val, q_val, d)
    } else {
        // fallback: identity
        let n = arr.len();
        (n, k_val, q_val, arr)
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

// Each case: (n, k, q, a)
type Case = (usize, usize, i64, Vec<i64>);

fn build_input(cases: &[Case]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (n, k, q, a) in cases {
        s.push_str(&format!("{} {} {}\n", n, k, q));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[i64]) -> String {
    let mut s = String::new();
    for a in answers { s.push_str(&format!("{}\n", a)); }
    s
}

fn random_case(rng: &mut Rng, max_n: usize) -> Case {
    let n = rng.gen_range_usize(1, max_n);
    let k = rng.gen_range_usize(1, n);
    let q = rng.gen_range_i64(-1_000_000_000, 1_000_000_000);
    let a: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(-1_000_000_000, 1_000_000_000)).collect();
    (n, k, q, a)
}

fn solve(c: &Case) -> i64 {
    Solution::count_vacations(c.0, c.1, c.2, c.3.clone())
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1840);
    let mut seen: HashSet<String> = HashSet::new();

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // Examples
    let example: Vec<Case> = vec![
        (3, 1, 15, vec![-5, 0, -10]),
        (5, 3, -3, vec![8, 12, 9, 0, 5]),
        (4, 3, 12, vec![12, 12, 10, 15]),
        (4, 1, -5, vec![0, -1, 2, 5]),
        (5, 5, 0, vec![3, -1, 4, -5, -3]),
        (1, 1, 56, vec![6]),
        (6, 1, 3, vec![0, 3, -2, 5, -4, -4]),
    ];
    {
        let inp = build_input(&example);
        let answers: Vec<i64> = example.iter().map(|c| solve(c)).collect();
        let outs = build_output(&answers);
        if seen.insert(inp.clone()) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
            count += 1;
        }
    }

    // Single-test edge cases
    let edges: Vec<Case> = vec![
        (1, 1, 0, vec![0]),
        (1, 1, -1_000_000_000, vec![1_000_000_000]),
        (1, 1, 1_000_000_000, vec![-1_000_000_000]),
        (5, 5, 0, vec![0, 0, 0, 0, 0]),
        (5, 1, -1, vec![0, 0, 0, 0, 0]), // none allowed
        (10, 3, 100, (0..10).map(|_| 50i64).collect()),
    ];
    for ec in &edges {
        if count >= target { break; }
        let cases = vec![ec.clone()];
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i64> = cases.iter().map(|c| solve(c)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }

    // Bundled multi-test
    while count < target {
        let t: usize = if count < 30 { rng.gen_range_usize(2, 6) } else { rng.gen_range_usize(3, 15) };
        let mut cases: Vec<Case> = Vec::new();
        let mut total_n = 0usize;
        for _ in 0..t {
            let max_n = if total_n < 100_000 { 200 } else { 50 };
            let c = random_case(&mut rng, max_n);
            if total_n + c.0 > 200_000 { break; }
            total_n += c.0;
            cases.push(c);
        }
        if cases.is_empty() { continue; }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i64> = cases.iter().map(|c| solve(c)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

