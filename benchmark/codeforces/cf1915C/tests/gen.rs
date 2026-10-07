use vstd::prelude::*;

verus! {

pub fn generate_test_case(a: Vec<i64>, mutation_kind: u8) -> (result: Vec<i64>)
    requires
        1 <= a.len() <= 200_000,
        forall|k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= 1_000_000_000,
    ensures
        1 <= result.len() <= 200_000,
        forall|k: int| 0 <= k < result.len() ==> 1 <= #[trigger] result[k] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        a
    } else if mutation_kind == 1 {
        // set first element to 1 (min boundary)
        let mut d = a;
        d.set(0, 1);
        d
    } else if mutation_kind == 2 {
        // set first element to 1_000_000_000 (max boundary)
        let mut d = a;
        d.set(0, 1_000_000_000);
        d
    } else if mutation_kind == 3 {
        // nudge first element up (if < max)
        let mut d = a;
        if d[0] < 1_000_000_000 {
            d.set(0, d[0] + 1);
        }
        d
    } else if mutation_kind == 4 {
        // nudge first element down (if > 1)
        let mut d = a;
        if d[0] > 1 {
            d.set(0, d[0] - 1);
        }
        d
    } else if mutation_kind == 5 {
        // set all elements to 1
        let mut d = a;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == a.len(),
                1 <= d.len() <= 200_000,
                forall|j: int| 0 <= j < i ==> d[j] == 1i64,
                forall|j: int| i <= j < d.len() ==> d[j] == a[j],
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        d
    } else if mutation_kind == 6 {
        // set all elements to 1_000_000_000
        let mut d = a;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == a.len(),
                1 <= d.len() <= 200_000,
                forall|j: int| 0 <= j < i ==> d[j] == 1_000_000_000i64,
                forall|j: int| i <= j < d.len() ==> d[j] == a[j],
            decreases d.len() - i,
        {
            d.set(i, 1_000_000_000);
            i += 1;
        }
        d
    } else if mutation_kind == 7 && a.len() < 200_000 {
        // grow by one element
        let mut d = a;
        d.push(1);
        d
    } else if mutation_kind == 8 && a.len() > 1 {
        // shrink by one element
        let mut d = a;
        d.pop();
        d
    } else if mutation_kind == 9 && a.len() >= 2 {
        // swap first two elements
        let mut d = a;
        let tmp = d[0];
        d.set(0, d[1]);
        d.set(1, tmp);
        d
    } else {
        // fallback
        a
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

fn build_input(cases: &[Vec<i64>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for a in cases {
        s.push_str(&format!("{}\n", a.len()));
        let p: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&p.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[bool]) -> String {
    let mut s = String::new();
    for &a in answers {
        s.push_str(if a {"YES\n"} else {"NO\n"});
    }
    s
}

fn random_case(rng: &mut Rng, max_n: usize) -> Vec<i64> {
    let n = rng.gen_range_usize(1, max_n);
    (0..n).map(|_| rng.gen_range_i64(1, 1_000_000_000)).collect()
}

// Generate a case whose sum is a perfect square
fn perfect_square_case(rng: &mut Rng) -> Vec<i64> {
    let s = rng.gen_range_i64(1, 14_000) as i64;
    let total: i64 = s * s;
    // Distribute total among 1..n buckets
    let n = rng.gen_range_usize(1, 10);
    let mut buckets = vec![0i64; n];
    let mut rem = total;
    for i in 0..n - 1 {
        let max_v = (rem - (n - 1 - i) as i64).min(1_000_000_000);
        if max_v < 1 { buckets[i] = 1; rem -= 1; continue; }
        let v = rng.gen_range_i64(1, max_v);
        buckets[i] = v;
        rem -= v;
    }
    buckets[n - 1] = rem.max(1);
    if buckets[n - 1] > 1_000_000_000 {
        // Just emit single bucket
        return vec![total];
    }
    buckets
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1915);
    let mut seen: HashSet<String> = HashSet::new();

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let example: Vec<Vec<i64>> = vec![
        vec![9],
        vec![1, 2, 3, 4, 5, 6, 7],     // sum=28, not square
        vec![1, 3, 5, 7, 9, 11],        // sum=36, square
        vec![2, 2, 2, 2],               // sum=8
        vec![14, 2],                    // sum=16, square
    ];
    {
        let inp = build_input(&example);
        let answers: Vec<bool> = example.iter().map(|a| Solution::can_square(a.clone())).collect();
        let outs = build_output(&answers);
        if seen.insert(inp.clone()) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
            count += 1;
        }
    }

    let edges: Vec<Vec<i64>> = vec![
        vec![1],
        vec![4],
        vec![2],
        vec![1, 3],
        vec![1_000_000_000],
        vec![1_000_000_000; 200],
    ];
    for ec in &edges {
        if count >= target { break; }
        let cases = vec![ec.clone()];
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<bool> = cases.iter().map(|a| Solution::can_square(a.clone())).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }

    while count < target {
        let t: usize = if count < 30 { rng.gen_range_usize(2, 6) } else { rng.gen_range_usize(3, 15) };
        let mut cases: Vec<Vec<i64>> = Vec::new();
        let mut total_n = 0usize;
        for _ in 0..t {
            let mut arr = if rng.next_u64() % 3 == 0 {
                perfect_square_case(&mut rng)
            } else {
                random_case(&mut rng, 50)
            };
            if total_n + arr.len() > 200_000 { break; }
            // ensure sum <= 14_000^2 since hi = 15_000_000 in code
            let s: i128 = arr.iter().map(|&x| x as i128).sum();
            if s > 200_000_000_000_000 {
                arr = vec![1, 3];  // fallback
            }
            total_n += arr.len();
            cases.push(arr);
        }
        if cases.is_empty() { continue; }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<bool> = cases.iter().map(|a| Solution::can_square(a.clone())).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

