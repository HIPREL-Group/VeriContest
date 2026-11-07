use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    raw: Vec<u32>,
    mutation_kind: u8,
) -> (result: (Vec<u32>, usize))
    requires
        1 <= raw.len() <= 200_000,
        forall|i: int| 0 <= i < raw.len() ==> 1 <= #[trigger] raw[i] <= 1_000_000_000,
    ensures
        1 <= result.1 <= 200_000,
        result.0.len() == result.1,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1_000_000_000,
{
    let n = raw.len();
    let mut a = raw;
    if mutation_kind == 0 {
        // identity
    } else if mutation_kind == 1 {
        // make all odd: round to next odd
        let mut i: usize = 0;
        while i < n
            invariant
                a.len() == n,
                1 <= n <= 200_000,
                0 <= i <= n,
                forall|j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j] <= 1_000_000_000,
            decreases n - i,
        {
            if a[i] % 2 == 0 {
                if a[i] < 1_000_000_000 {
                    a.set(i, a[i] + 1);
                } else {
                    a.set(i, a[i] - 1);
                }
            }
            i += 1;
        }
    } else if mutation_kind == 2 {
        // make all even
        let mut i: usize = 0;
        while i < n
            invariant
                a.len() == n,
                1 <= n <= 200_000,
                0 <= i <= n,
                forall|j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j] <= 1_000_000_000,
            decreases n - i,
        {
            if a[i] % 2 == 1 {
                if a[i] >= 2 {
                    a.set(i, a[i] - 1);
                } else {
                    a.set(i, a[i] + 1);
                }
            }
            i += 1;
        }
    } else if mutation_kind == 3 {
        // alternate: even at 0, odd at 1, ...
        let mut i: usize = 0;
        while i < n
            invariant
                a.len() == n,
                1 <= n <= 200_000,
                0 <= i <= n,
                forall|j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j] <= 1_000_000_000,
            decreases n - i,
        {
            a.set(i, ((i % 2) + 2) as u32);
            i += 1;
        }
    } else {
        // identity
    }
    (a, n)
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
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
    fn gen_range_u32(&mut self, lo: u32, hi: u32) -> u32 {
        let r = (hi as u64 - lo as u64 + 1);
        lo + (self.next_u64() % r) as u32
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

fn build_input(cases: &[Vec<u32>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for a in cases {
        s.push_str(&format!("{}\n", a.len()));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[bool]) -> String {
    let mut s = String::new();
    for &b in answers {
        s.push_str(if b { "YES\n" } else { "NO\n" });
    }
    s
}

fn solve(a: &Vec<u32>) -> bool {
    Solution::vlad_beautiful(a.clone(), a.len())
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1833);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);

    // Sample
    {
        let cases: Vec<Vec<u32>> = vec![
            vec![2, 6, 8, 4, 3],
            vec![1, 4, 7, 6, 9],
            vec![2, 6, 4, 10],
            vec![5, 29, 13, 9, 1000001],
            vec![1, 11, 3],
            vec![2, 1, 2, 4, 2],
            vec![2, 4, 5, 4, 3],
            vec![2, 5, 5, 4],
        ];
        let inp = build_input(&cases);
        if seen.insert(inp.clone()) {
            let answers: Vec<bool> = cases.iter().map(|a| solve(a)).collect();
            let outp = build_output(&answers);
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        }
    }

    let mut count = 1usize;
    while count < target {
        let t = rng.gen_range_usize(1, 8);
        let mut cases: Vec<Vec<u32>> = Vec::new();
        for _ in 0..t {
            let n = match rng.next_u64() % 5 {
                0 => rng.gen_range_usize(1, 5),
                1 => rng.gen_range_usize(1, 20),
                2 => rng.gen_range_usize(20, 100),
                3 => rng.gen_range_usize(50, 500),
                _ => rng.gen_range_usize(100, 1000),
            };
            let arr: Vec<u32> = (0..n).map(|_| rng.gen_range_u32(1, 1000)).collect();
            cases.push(arr);
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<bool> = cases.iter().map(|a| solve(a)).collect();
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
