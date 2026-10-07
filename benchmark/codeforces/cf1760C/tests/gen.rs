use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<i64>, mutation_kind: u8) -> (result: Vec<i64>)
    requires
        2 <= values.len() <= 200_000,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1_000_000_000,
    ensures
        2 <= result.len() <= 200_000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        values
    } else if mutation_kind == 1 {
        // set first element to 1 (min boundary)
        let mut v = values;
        v.set(0, 1);
        v
    } else if mutation_kind == 2 {
        // set first element to 1_000_000_000 (max boundary)
        let mut v = values;
        v.set(0, 1_000_000_000);
        v
    } else if mutation_kind == 3 {
        // set all elements to the first element's value
        let val = values[0];
        let len = values.len();
        let mut v = values;
        let mut i: usize = 1;
        while i < len
            invariant
                1 <= i <= len,
                v.len() == len,
                2 <= len <= 200_000,
                1 <= val <= 1_000_000_000,
                forall|j: int| 0 <= j < i as int ==> #[trigger] v[j] == val,
                forall|j: int| i as int <= j < len as int ==> #[trigger] v[j] == values[j],
            decreases len - i,
        {
            v.set(i, val);
            i += 1;
        }
        v
    } else if mutation_kind == 4 && values.len() < 200_000 {
        // grow by one element (push 1)
        let mut v = values;
        v.push(1);
        v
    } else if mutation_kind == 5 && values.len() > 2 {
        // shrink by one element (pop)
        let mut v = values;
        v.pop();
        v
    } else if mutation_kind == 6 && values.len() >= 2 {
        // swap first two elements
        let mut v = values;
        let a = v[0];
        let b = v[1];
        v.set(0, b);
        v.set(1, a);
        v
    } else if mutation_kind == 7 {
        // set last element to 1 (min boundary)
        let mut v = values;
        let last = v.len() - 1;
        v.set(last, 1);
        v
    } else if mutation_kind == 8 {
        // set last element to 1_000_000_000 (max boundary)
        let mut v = values;
        let last = v.len() - 1;
        v.set(last, 1_000_000_000);
        v
    } else {
        // fallback: identity
        values
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

type TC = Vec<i64>;

fn build_input(cases: &[TC]) -> String {
    let mut s = format!("{}\n", cases.len());
    for a in cases {
        s.push_str(&format!("{}\n", a.len()));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(cases: &[TC]) -> String {
    let mut s = String::new();
    for a in cases {
        let ans = Solution::advantages(a.clone());
        let parts: Vec<String> = ans.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn random_a(rng: &mut Rng, n: usize, max_v: i64) -> Vec<i64> {
    (0..n).map(|_| rng.gen_range_i64(1, max_v)).collect()
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1760);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let examples: Vec<TC> = vec![
        vec![4, 7, 3, 5],
        vec![1, 2],
        vec![1, 2, 3, 4, 5],
        vec![4, 9, 4],
        vec![4, 4, 4, 4],
        vec![1, 1],
        vec![1000000000, 1],
        vec![5, 4, 3, 2, 1],
    ];

    for ex in &examples {
        if count >= target { break; }
        let cases = vec![ex.clone()];
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }

    while count < target {
        let t: usize = if count < 20 { rng.gen_range_usize(1, 5) } else { rng.gen_range_usize(2, 30) };
        let mut cases: Vec<TC> = Vec::new();
        for _ in 0..t {
            let n = match rng.gen_range_usize(0, 4) {
                0 => rng.gen_range_usize(2, 5),
                1 => rng.gen_range_usize(2, 30),
                2 => rng.gen_range_usize(50, 200),
                _ => rng.gen_range_usize(2, 100),
            };
            cases.push(random_a(&mut rng, n, 1_000_000_000));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

