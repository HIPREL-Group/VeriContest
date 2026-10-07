use vstd::prelude::*;

verus! {

/// Generates a valid input vector `c` for the min_chip_teleports problem.
///
/// Construction: takes a base value for c[0] (>= 1), a vector of element
/// values for the remaining positions, and a mutation_kind selector.
pub fn generate_test_case(
    first: i64,
    rest: Vec<i64>,
    mutation_kind: u8,
) -> (result: Vec<i64>)
    requires
        1 <= first as int <= 1_000_000_000,
        rest.len() <= 199_999,
        forall|i: int| 0 <= i < rest.len() ==> 0 <= #[trigger] rest[i] as int <= 1_000_000_000,
    ensures
        1 <= result.len() <= 200_000,
        forall|i: int|
            0 <= i < result.len() as int ==> 0 <= #[trigger] result[i] as int <= 1_000_000_000,
        result[0] as int >= 1,
{
    let mut c: Vec<i64> = Vec::new();
    c.push(first);

    // Append rest elements
    let mut j: usize = 0;
    while j < rest.len()
        invariant
            1 <= c.len() <= 1 + j,
            c.len() == 1 + j,
            j <= rest.len(),
            rest.len() <= 199_999,
            c[0] == first,
            first as int >= 1,
            first as int <= 1_000_000_000,
            forall|k: int| 0 <= k < c.len() ==> 0 <= #[trigger] c[k] as int <= 1_000_000_000,
            forall|k: int| 0 <= k < rest.len() ==> 0 <= #[trigger] rest[k] as int <= 1_000_000_000,
        decreases rest.len() - j,
    {
        c.push(rest[j]);
        j = j + 1;
    }
    // c.len() == 1 + rest.len() <= 200_000

    if mutation_kind == 0 {
        // identity
        c
    } else if mutation_kind == 1 && c.len() > 1 {
        // set last element to 0
        let last = c.len() - 1;
        c.set(last, 0i64);
        c
    } else if mutation_kind == 2 && c.len() > 1 {
        // set last element to max (1_000_000_000)
        let last = c.len() - 1;
        c.set(last, 1_000_000_000i64);
        c
    } else if mutation_kind == 3 {
        // set first element to 1 (minimum valid)
        c.set(0, 1i64);
        c
    } else if mutation_kind == 4 {
        // set first element to max (1_000_000_000)
        c.set(0, 1_000_000_000i64);
        c
    } else if mutation_kind == 5 && c.len() > 1 {
        // pop last element (shrink)
        c.pop();
        c
    } else if mutation_kind == 6 && c.len() < 200_000 {
        // push a 0 element (grow)
        c.push(0i64);
        c
    } else if mutation_kind == 7 {
        // set all elements (except first) to same value as first
        let val = c[0];
        let mut i: usize = 1;
        while i < c.len()
            invariant
                1 <= i <= c.len(),
                c.len() == 1 + rest.len(),
                1 + rest.len() <= 200_000,
                c[0] == first,
                first as int >= 1,
                first as int <= 1_000_000_000,
                val == first,
                forall|k: int| 0 <= k < c.len() ==> 0 <= #[trigger] c[k] as int <= 1_000_000_000,
            decreases c.len() - i,
        {
            c.set(i, val);
            i = i + 1;
        }
        c
    } else {
        // fallback: identity
        c
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
    for c in cases {
        s.push_str(&format!("{}\n", c.len()));
        let p: Vec<String> = c.iter().map(|x| x.to_string()).collect();
        s.push_str(&p.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[i64]) -> String {
    let mut s = String::new();
    for a in answers { s.push_str(&format!("{}\n", a)); }
    s
}

fn random_case(rng: &mut Rng, max_n: usize, max_v: i64) -> Vec<i64> {
    let n = rng.gen_range_usize(1, max_n);
    let mut c: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(0, max_v)).collect();
    if c[0] < 1 { c[0] = 1; }
    c
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1901);
    let mut seen: HashSet<String> = HashSet::new();

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let example: Vec<Vec<i64>> = vec![
        vec![1, 2, 2, 1],
        vec![1, 0, 1, 0, 1],
        vec![1, 2, 3, 4, 5],
        vec![1, 12],
    ];
    {
        let inp = build_input(&example);
        let answers: Vec<i64> = example.iter().map(|c| Solution::min_chip_teleports(c.clone())).collect();
        let outs = build_output(&answers);
        if seen.insert(inp.clone()) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
            count += 1;
        }
    }

    let edges: Vec<Vec<i64>> = vec![
        vec![1],
        vec![1_000_000_000],
        vec![1, 0],
        vec![1; 100],
        (1..=100).collect(),
    ];
    for ec in &edges {
        if count >= target { break; }
        let cases = vec![ec.clone()];
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i64> = cases.iter().map(|c| Solution::min_chip_teleports(c.clone())).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }

    while count < target {
        let t: usize = if count < 30 { rng.gen_range_usize(2, 6) } else { rng.gen_range_usize(3, 15) };
        let mut cases: Vec<Vec<i64>> = Vec::new();
        let mut total_n = 0usize;
        for _ in 0..t {
            let arr = random_case(&mut rng, 200, 1_000_000_000);
            if total_n + arr.len() > 200_000 { break; }
            total_n += arr.len();
            cases.push(arr);
        }
        if cases.is_empty() { continue; }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i64> = cases.iter().map(|c| Solution::min_chip_teleports(c.clone())).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

