use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    sa: Vec<i32>,
    sb: Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        2 <= sa.len() <= 200_000,
        sa.len() == sb.len(),
        forall|j: int| 0 <= j < sa.len() ==> -1_000_000_000 <= #[trigger] sa[j] <= 1_000_000_000,
        forall|j: int| 0 <= j < sb.len() ==> -1_000_000_000 <= #[trigger] sb[j] <= 1_000_000_000,
    ensures
        2 <= result.0.len() <= 200_000,
        result.0.len() == result.1.len(),
        forall|j: int| 0 <= j < result.0.len() ==> -1_000_000_000 <= #[trigger] result.0[j] <= 1_000_000_000,
        forall|j: int| 0 <= j < result.1.len() ==> -1_000_000_000 <= #[trigger] result.1[j] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        (sa, sb)
    } else if mutation_kind == 1 {
        // swap a and b
        (sb, sa)
    } else if mutation_kind == 2 {
        // set a[0] to 0
        let mut a = sa;
        a.set(0, 0);
        (a, sb)
    } else if mutation_kind == 3 {
        // set b[0] to 0
        let mut b = sb;
        b.set(0, 0);
        (sa, b)
    } else if mutation_kind == 4 {
        // set a[0] to max boundary
        let mut a = sa;
        a.set(0, 1_000_000_000);
        (a, sb)
    } else if mutation_kind == 5 {
        // set b[0] to min boundary
        let mut b = sb;
        b.set(0, -1_000_000_000);
        (sa, b)
    } else if mutation_kind == 6 {
        // set a[0] = b[0] (make first diff = 0)
        let mut a = sa;
        a.set(0, sb[0]);
        (a, sb)
    } else if mutation_kind == 7 && sa[0] < 1_000_000_000 {
        // nudge a[0] up
        let val = sa[0] + 1;
        let mut a = sa;
        a.set(0, val);
        (a, sb)
    } else if mutation_kind == 8 && sb[0] > -1_000_000_000 {
        // nudge b[0] down
        let val = sb[0] - 1;
        let mut b = sb;
        b.set(0, val);
        (sa, b)
    } else {
        // fallback: identity
        (sa, sb)
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

type Case = (Vec<i32>, Vec<i32>); // (a, b)

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

fn random_case(rng: &mut Rng, max_n: usize, max_v: i32) -> Case {
    let n = rng.gen_range_usize(2, max_n);
    let a: Vec<i32> = (0..n).map(|_| rng.gen_range_i64(-max_v as i64, max_v as i64) as i32).collect();
    let b: Vec<i32> = (0..n).map(|_| rng.gen_range_i64(-max_v as i64, max_v as i64) as i32).collect();
    (a, b)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1857);
    let mut seen: HashSet<String> = HashSet::new();

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // Example
    let example: Vec<Case> = vec![
        (vec![3, 1, 2, 4], vec![4, 3, 2, 1]),
        (vec![1, 2, 4, 1, 2], vec![5, 2, 3, 3, 1]),
        (vec![1, 2], vec![2, 1]),
        (vec![0, 2, 1], vec![1, 3, 2]),
        (vec![5, 7, 4], vec![-2, -3, -6]),
    ];
    {
        let inp = build_input(&example);
        let answers: Vec<Vec<i32>> = example.iter().map(|c| solve(c)).collect();
        let outs = build_output(&answers);
        if seen.insert(inp.clone()) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
            count += 1;
        }
    }

    // Edges
    let edges: Vec<Case> = vec![
        (vec![0, 0], vec![0, 0]),  // all zero
        (vec![1, 2], vec![1, 2]),  // d all zero
        (vec![1_000_000_000, -1_000_000_000], vec![-1_000_000_000, 1_000_000_000]),
    ];
    for ec in &edges {
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
        let t: usize = if count < 30 { rng.gen_range_usize(2, 6) } else { rng.gen_range_usize(3, 15) };
        let mut cases: Vec<Case> = Vec::new();
        let mut total_n = 0usize;
        for _ in 0..t {
            let n = rng.gen_range_usize(2, 200);
            if total_n + n > 200_000 { break; }
            total_n += n;
            cases.push(random_case(&mut rng, n + 1, 1_000_000_000));
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

