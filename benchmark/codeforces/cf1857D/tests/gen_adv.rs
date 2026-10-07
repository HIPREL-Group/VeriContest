use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    a_vals: &Vec<i32>,
    b_vals: &Vec<i32>,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        2 <= a_vals.len() <= 200_000,
        a_vals.len() == b_vals.len(),
        forall|j: int| 0 <= j < a_vals.len() ==> -1_000_000_000 <= #[trigger] a_vals[j] <= 1_000_000_000,
        forall|j: int| 0 <= j < b_vals.len() ==> -1_000_000_000 <= #[trigger] b_vals[j] <= 1_000_000_000,
    ensures
        ({
            let (a, b) = result;
            &&& 2 <= a.len() <= 200_000
            &&& a.len() == b.len()
            &&& (forall|j: int| 0 <= j < a.len() ==> -1_000_000_000 <= #[trigger] a[j] <= 1_000_000_000)
            &&& (forall|j: int| 0 <= j < b.len() ==> -1_000_000_000 <= #[trigger] b[j] <= 1_000_000_000)
        }),
{
    let n = a_vals.len();
    let mut a: Vec<i32> = Vec::new();
    let mut b: Vec<i32> = Vec::new();

    let mut i: usize = 0;
    while i < n
        invariant
            n == a_vals.len(),
            n == b_vals.len(),
            2 <= n <= 200_000,
            0 <= i <= n,
            a.len() == i,
            b.len() == i,
            forall|k: int| 0 <= k < i as int ==> #[trigger] a[k] == a_vals[k],
            forall|k: int| 0 <= k < i as int ==> #[trigger] b[k] == b_vals[k],
            forall|j: int| 0 <= j < a_vals.len() ==> -1_000_000_000 <= #[trigger] a_vals[j] <= 1_000_000_000,
            forall|j: int| 0 <= j < b_vals.len() ==> -1_000_000_000 <= #[trigger] b_vals[j] <= 1_000_000_000,
        decreases n - i,
    {
        a.push(a_vals[i]);
        b.push(b_vals[i]);
        i = i + 1;
    }

    (a, b)
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

type Case = (Vec<i32>, Vec<i32>);

fn build_input(cases: &[Case]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (a, b) in cases {
        s.push_str(&format!("{}\n", a.len()));
        let pa: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&pa.join(" "));
        s.push('\n');
        let pb: Vec<String> = b.iter().map(|x| x.to_string()).collect();
        s.push_str(&pb.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[Vec<i32>]) -> String {
    let mut s = String::new();
    for ans in answers {
        s.push_str(&format!("{}\n", ans.len()));
        for (j, v) in ans.iter().enumerate() {
            if j > 0 { s.push(' '); }
            s.push_str(&v.to_string());
        }
        s.push('\n');
    }
    s
}

fn solve(c: &Case) -> Vec<i32> {
    Solution::strong_vertices(c.0.clone(), c.1.clone())
}

fn random_case(rng: &mut Rng, n: usize, max_v: i32) -> Case {
    let a: Vec<i32> = (0..n).map(|_| rng.gen_range_i64(-max_v as i64, max_v as i64) as i32).collect();
    let b: Vec<i32> = (0..n).map(|_| rng.gen_range_i64(-max_v as i64, max_v as i64) as i32).collect();
    (a, b)
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(31415);
    let mut seen: HashSet<String> = HashSet::new();

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // Big single
    let big_singles: Vec<Case> = vec![
        (vec![1; 10000], vec![1; 10000]),  // all equal d -> all are strong
        ((0..10000).map(|i| i as i32).collect(), (0..10000).map(|i| -(i as i32)).collect()),  // monotonic
        ((0..10000).map(|i| -(i as i32)).collect(), (0..10000).map(|i| i as i32).collect()),  // monotonic neg
    ];
    for ec in &big_singles {
        if count >= target { break; }
        let cases = vec![ec.clone()];
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<Vec<i32>> = cases.iter().map(|c| solve(c)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }

    while count < target {
        let mode = rng.next_u64() % 4;
        let mut cases: Vec<Case> = Vec::new();
        let mut total_n = 0usize;
        match mode {
            0 => {
                let t = rng.gen_range_usize(20, 100);
                for _ in 0..t {
                    let n = rng.gen_range_usize(2, 30);
                    if total_n + n > 200_000 { break; }
                    total_n += n;
                    cases.push(random_case(&mut rng, n, 1_000_000_000));
                }
            }
            1 => {
                let t = rng.gen_range_usize(2, 5);
                for _ in 0..t {
                    let n = rng.gen_range_usize(5000, 20_000);
                    if total_n + n > 200_000 { break; }
                    total_n += n;
                    cases.push(random_case(&mut rng, n, 1_000_000_000));
                }
            }
            2 => {
                let n = rng.gen_range_usize(50_000, 100_000);
                cases.push(random_case(&mut rng, n, 1_000_000_000));
            }
            _ => {
                let t = rng.gen_range_usize(5, 30);
                for _ in 0..t {
                    let n = rng.gen_range_usize(2, 1000);
                    if total_n + n > 200_000 { break; }
                    total_n += n;
                    cases.push(random_case(&mut rng, n, 1_000_000_000));
                }
            }
        }
        if cases.is_empty() { continue; }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<Vec<i32>> = cases.iter().map(|c| solve(c)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

