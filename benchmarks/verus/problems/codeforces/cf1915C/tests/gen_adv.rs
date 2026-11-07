use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    fillers: &Vec<i64>,
) -> (a: Vec<i64>)
    requires
        1 <= fillers.len() <= 200_000,
        forall |k: int| 0 <= k < fillers.len() ==> 1 <= #[trigger] fillers[k] <= 1_000_000_000,
    ensures
        1 <= a.len() <= 200_000,
        a.len() == fillers.len(),
        forall |k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= 1_000_000_000,
{
    let n = fillers.len();
    let mut a: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == fillers.len(),
            1 <= n <= 200_000,
            0 <= i <= n,
            a.len() == i,
            forall |k: int| 0 <= k < fillers.len() ==> 1 <= #[trigger] fillers[k] <= 1_000_000_000,
            forall |k: int| 0 <= k < i as int ==> #[trigger] a[k] == fillers[k],
        decreases n - i,
    {
        a.push(fillers[i]);
        i = i + 1;
    }
    a
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

fn perfect_square_case(rng: &mut Rng, max_n: usize) -> Vec<i64> {
    let s = rng.gen_range_i64(1, 14_000) as i64;
    let total: i64 = s * s;
    let n = rng.gen_range_usize(1, max_n);
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
        return vec![total.min(1_000_000_000)];
    }
    buckets
}

fn random_case(rng: &mut Rng, n: usize) -> Vec<i64> {
    (0..n).map(|_| rng.gen_range_i64(1, 1_000_000_000)).collect()
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(31415);
    let mut seen: HashSet<String> = HashSet::new();

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    while count < target {
        let mode = rng.next_u64() % 4;
        let mut cases: Vec<Vec<i64>> = Vec::new();
        let mut total_n = 0usize;
        match mode {
            0 => {
                let t = rng.gen_range_usize(20, 100);
                for _ in 0..t {
                    let arr = if rng.next_u64() % 2 == 0 {
                        perfect_square_case(&mut rng, 5)
                    } else {
                        let n2 = rng.gen_range_usize(1, 5);
                        random_case(&mut rng, n2)
                    };
                    if total_n + arr.len() > 200_000 { break; }
                    total_n += arr.len();
                    cases.push(arr);
                }
            }
            1 => {
                let t = rng.gen_range_usize(2, 5);
                for _ in 0..t {
                    let n = rng.gen_range_usize(1000, 30_000);
                    if total_n + n > 200_000 { break; }
                    total_n += n;
                    cases.push(random_case(&mut rng, n));
                }
            }
            2 => {
                let n = rng.gen_range_usize(50_000, 100_000);
                cases.push(random_case(&mut rng, n));
            }
            _ => {
                let t = rng.gen_range_usize(5, 30);
                for _ in 0..t {
                    let arr = if rng.next_u64() % 3 == 0 {
                        perfect_square_case(&mut rng, 100)
                    } else {
                        let n2 = rng.gen_range_usize(1, 200);
                        random_case(&mut rng, n2)
                    };
                    if total_n + arr.len() > 200_000 { break; }
                    total_n += arr.len();
                    cases.push(arr);
                }
            }
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

