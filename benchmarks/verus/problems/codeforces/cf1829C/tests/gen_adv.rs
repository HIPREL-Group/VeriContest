use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    times: &Vec<i32>,
    masks: &Vec<i32>,
    target: i32,
) -> (result: (Vec<i32>, Vec<i32>, i32))
    requires
        1 <= times.len() <= 200_000,
        times.len() == masks.len(),
        forall|i: int| 0 <= i < times.len() ==> 1 <= #[trigger] times[i] <= 200_000,
        forall|i: int| 0 <= i < masks.len() ==> 0 <= #[trigger] masks[i] <= 3,
    ensures
        ({
            let (m, s, t) = result;
            &&& 1 <= m.len() <= 200_000
            &&& m.len() == s.len()
            &&& (forall|i: int| 0 <= i < m.len() ==> 1 <= #[trigger] m[i] <= 200_000)
            &&& (forall|i: int| 0 <= i < s.len() ==> 0 <= #[trigger] s[i] <= 3)
            &&& t == target
        }),
{
    let mut m: Vec<i32> = Vec::new();
    let mut s: Vec<i32> = Vec::new();
    let n = times.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == times.len(),
            times.len() == masks.len(),
            0 <= i <= n,
            m.len() == i,
            s.len() == i,
            forall|k: int| 0 <= k < i as int ==> 1 <= #[trigger] m[k] <= 200_000,
            forall|k: int| 0 <= k < i as int ==> 0 <= #[trigger] s[k] <= 3,
            forall|k: int| 0 <= k < times.len() ==> 1 <= #[trigger] times[k] <= 200_000,
            forall|k: int| 0 <= k < masks.len() ==> 0 <= #[trigger] masks[k] <= 3,
        decreases n - i,
    {
        m.push(times[i]);
        s.push(masks[i]);
        i = i + 1;
    }
    (m, s, target)
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

fn mask_to_bits(mask: i32) -> &'static str {
    match mask {
        3 => "11",
        2 => "10",
        1 => "01",
        _ => "00",
    }
}

fn build_input(cases: &[Vec<(i32, i32)>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for c in cases {
        s.push_str(&format!("{}\n", c.len()));
        for &(m, mask) in c {
            s.push_str(&format!("{} {}\n", m, mask_to_bits(mask)));
        }
    }
    s
}

fn build_output(answers: &[i32]) -> String {
    let mut s = String::new();
    for a in answers {
        s.push_str(&format!("{}\n", a));
    }
    s
}

fn random_case(rng: &mut Rng, n: usize, max_m: i32, mask_bias: u8) -> Vec<(i32, i32)> {
    (0..n).map(|_| {
        let m = rng.gen_range_i64(1, max_m as i64) as i32;
        let mask = match mask_bias {
            0 => (rng.next_u64() % 4) as i32,
            1 => (rng.next_u64() % 3) as i32,  // bias to 0/1/2
            2 => if rng.next_u64() % 2 == 0 { 1 } else { 2 }, // only 01/10
            _ => 3, // only 11
        };
        (m, mask)
    }).collect()
}

fn solve(case: &[(i32, i32)]) -> i32 {
    let m: Vec<i32> = case.iter().map(|&(m, _)| m).collect();
    let s: Vec<i32> = case.iter().map(|&(_, s)| s).collect();
    Solution::min_minutes(m, s)
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(31415);
    let mut seen: HashSet<String> = HashSet::new();

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // Big single-cases
    let big_singles: Vec<Vec<(i32, i32)>> = vec![
        // Lots of skill 1 only
        (0..1000).map(|i| (i + 1, 2)).collect(),
        // Lots of skill 2 only -> -1
        (0..1000).map(|i| (i + 1, 1)).collect(),
        // Many books with both
        (0..1000).map(|i| (1000 - i, 3)).collect(),
        // All zero skills
        (0..1000).map(|i| (i + 1, 0)).collect(),
        // Mix
        (0..1000).map(|i| (i + 1, (i % 4) as i32)).collect(),
    ];
    for c in &big_singles {
        if count >= target { break; }
        let cases = vec![c.clone()];
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i32> = cases.iter().map(|c| solve(c)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }

    while count < target {
        let mode = rng.next_u64() % 5;
        let mut cases: Vec<Vec<(i32, i32)>> = Vec::new();
        let mut total_n = 0usize;
        match mode {
            0 => {
                // Many small cases
                let t = rng.gen_range_usize(20, 100);
                for _ in 0..t {
                    let n = rng.gen_range_usize(1, 10);
                    if total_n + n > 200_000 { break; }
                    total_n += n;
                    cases.push(random_case(&mut rng, n, 200_000, 0));
                }
            }
            1 => {
                // Few large
                let t = rng.gen_range_usize(2, 10);
                for _ in 0..t {
                    let n = rng.gen_range_usize(1000, 10_000);
                    if total_n + n > 200_000 { break; }
                    total_n += n;
                    cases.push(random_case(&mut rng, n, 200_000, 0));
                }
            }
            2 => {
                // One huge
                let n = rng.gen_range_usize(50_000, 200_000);
                cases.push(random_case(&mut rng, n, 200_000, 0));
            }
            3 => {
                // Mask-biased
                let t = rng.gen_range_usize(5, 20);
                for _ in 0..t {
                    let n = rng.gen_range_usize(1, 100);
                    if total_n + n > 200_000 { break; }
                    total_n += n;
                    let bias = (rng.next_u64() % 4) as u8;
                    cases.push(random_case(&mut rng, n, 200_000, bias));
                }
            }
            _ => {
                let t = rng.gen_range_usize(5, 50);
                for _ in 0..t {
                    let n = rng.gen_range_usize(1, 200);
                    if total_n + n > 200_000 { break; }
                    total_n += n;
                    cases.push(random_case(&mut rng, n, 200_000, 0));
                }
            }
        }
        if cases.is_empty() { continue; }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i32> = cases.iter().map(|c| solve(c)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

