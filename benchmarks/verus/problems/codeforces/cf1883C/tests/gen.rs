use vstd::prelude::*;

verus! {

pub fn generate_test_case(raw: Vec<i32>, k: i32) -> (result: (usize, i32, Vec<i32>))
    ensures
        2 <= result.0 <= 100000,
        2 <= result.1 <= 5,
        result.2.len() == result.0,
        forall|j: int| 0 <= j < result.2.len() ==> 1 <= #[trigger] result.2[j] <= 10,
{
    let n = if raw.len() < 2 { 2usize } else if raw.len() > 100000 { 100000usize } else { raw.len() };
    let k = if k < 2 { 2 } else if k > 5 { 5 } else { k };
    let mut a: Vec<i32> = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            2 <= n <= 100000, 0 <= i <= n, a.len() == i,
            forall|j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j] <= 10,
        decreases n - i,
    {
        let value = if i < raw.len() { raw[i] } else { 1 };
        a.push(if value < 1 { 1 } else if value > 10 { 10 } else { value });
        i += 1;
    }
    (n, k, a)
}


pub fn generate_candidate(
    seed_a: Vec<i32>,
    n: usize,
    k: i32,
    mutation_kind: u8,
) -> (a: Vec<i32>)
    requires
        seed_a.len() == n,
        2 <= n && n <= 100000,
        2 <= k && k <= 5,
        forall|j: int| 0 <= j && j < n ==> 1 <= seed_a@[j] && seed_a@[j] <= 10,
    ensures
        2 <= n && n <= 100000,
        2 <= k && k <= 5,
        a.len() == n,
        forall|j: int| 0 <= j && j < n ==> 1 <= a@[j] && a@[j] <= 10,
{
    if mutation_kind == 0 {
        seed_a
    } else if mutation_kind == 1 {
        let mut r = seed_a;
        let last = n - 1;
        r.set(last, 1);
        r
    } else if mutation_kind == 2 {
        let mut r = seed_a;
        let last = n - 1;
        r.set(last, 10);
        r
    } else if mutation_kind == 3 && seed_a[n - 1] < 10 {
        let mut r = seed_a;
        let last = n - 1;
        r.set(last, r[last] + 1);
        r
    } else if mutation_kind == 4 && seed_a[n - 1] > 1 {
        let mut r = seed_a;
        let last = n - 1;
        r.set(last, r[last] - 1);
        r
    } else if mutation_kind == 5 {
        let mut r = seed_a;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                r.len() == n,
                2 <= n <= 100000,
                forall|j: int| 0 <= j < i as int ==> r@[j] == 1i32,
                forall|j: int| i as int <= j < n as int ==> r@[j] == seed_a@[j],
            decreases n - i,
        {
            r.set(i, 1);
            i = i + 1;
        }
        r
    } else if mutation_kind == 6 {
        let mut r = seed_a;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                r.len() == n,
                2 <= n <= 100000,
                forall|j: int| 0 <= j < i as int ==> r@[j] == 10i32,
                forall|j: int| i as int <= j < n as int ==> r@[j] == seed_a@[j],
            decreases n - i,
        {
            r.set(i, 10);
            i = i + 1;
        }
        r
    } else if mutation_kind == 7 {
        let mut r = seed_a;
        r.set(0, 5);
        r
    } else if mutation_kind == 8 {
        let mut r = seed_a;
        r.set(0, 1);
        r
    } else {
        seed_a
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

type Case = (usize, i32, Vec<i32>);

fn build_input(cases: &[Case]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (n, k, a) in cases {
        s.push_str(&format!("{} {}\n", n, k));
        let p: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&p.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[i32]) -> String {
    let mut s = String::new();
    for a in answers { s.push_str(&format!("{}\n", a)); }
    s
}

fn solve(c: &Case) -> i32 {
    Solution::min_ops(c.0, c.1, c.2.clone())
}

fn random_case(rng: &mut Rng, max_n: usize) -> Case {
    let n = rng.gen_range_usize(2, max_n);
    let k = (rng.gen_range_i64(2, 5)) as i32;
    let a: Vec<i32> = (0..n).map(|_| rng.gen_range_i64(1, 10) as i32).collect();
    (n, k, a)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1883);
    let mut seen: HashSet<String> = HashSet::new();

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // Example
    let example: Vec<Case> = vec![
        (2, 5, vec![7, 3]),
        (2, 4, vec![2, 2]),
        (3, 3, vec![4, 12, 7]),
    ];
    {
        let example: Vec<_> = example.iter().map(|c| generate_test_case(c.2.clone(), c.1)).collect();
        let inp = build_input(&example);
        let answers: Vec<i32> = example.iter().map(|c| solve(c)).collect();
        let outs = build_output(&answers);
        if seen.insert(inp.clone()) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
            count += 1;
        }
    }

    // Edges
    let edges: Vec<Case> = vec![
        (2, 2, vec![1, 1]),
        (2, 2, vec![2, 1]),
        (2, 3, vec![1, 1]),
        (2, 4, vec![1, 1]),
        (2, 5, vec![1, 1]),
        (5, 4, vec![3, 5, 7, 9, 1]),  // all odd, has 3mod4
        (5, 4, vec![1, 5, 9, 5, 1]),  // all 1mod4
        (10, 5, vec![10; 10]),
    ];
    for ec in &edges {
        if count >= target { break; }
        let cases = vec![ec.clone()];
        let cases: Vec<_> = cases.iter().map(|c| generate_test_case(c.2.clone(), c.1)).collect();
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i32> = cases.iter().map(|c| solve(c)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }

    while count < target {
        let t: usize = if count < 30 { rng.gen_range_usize(2, 8) } else { rng.gen_range_usize(5, 30) };
        let mut cases: Vec<Case> = Vec::new();
        let mut total_n = 0usize;
        for _ in 0..t {
            let c = random_case(&mut rng, 100);
            if total_n + c.0 > 200_000 { break; }
            total_n += c.0;
            cases.push(c);
        }
        if cases.is_empty() { continue; }
        let cases: Vec<_> = cases.iter().map(|c| generate_test_case(c.2.clone(), c.1)).collect();
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i32> = cases.iter().map(|c| solve(c)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}
