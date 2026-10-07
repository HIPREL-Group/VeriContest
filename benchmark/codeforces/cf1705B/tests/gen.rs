use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<i64>) -> (result: Vec<i64>)
    ensures
        2 <= result.len() <= 200000,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 1000000000,
{
    let n = if values.len() < 2 { 2usize }
            else if values.len() > 200000 { 200000usize } else { values.len() };
    let limit = 1000000000;
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            2 <= n <= 200000,
            limit == 1000000000,
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> 0 <= #[trigger] result[j] <= limit,
        decreases n - i,
    {
        let value = if i < values.len() { values[i] } else { 0 };
        let value = if value < 0 { 0 } else if value > limit { limit } else { value };
        result.push(value);
        i += 1;
    }
    result
}


pub fn generate_candidate(
    // Construction parameters: element values and desired length
    elems: Vec<i64>,
    mutation_kind: u8,
) -> (result: Vec<i64>)
    requires
        2 <= elems.len() <= 200000,
        forall|j: int| 0 <= j < elems.len() as int ==> 0 <= #[trigger] elems[j] as int <= 1000000000,
    ensures
        2 <= result.len() <= 200000,
        forall|j: int| 0 <= j < result.len() as int ==> 0 <= #[trigger] result[j] as int <= 1000000000,
{
    if mutation_kind == 0 {
        // identity
        elems
    } else if mutation_kind == 1 {
        // set first element to 0
        let mut v = elems;
        v.set(0, 0);
        v
    } else if mutation_kind == 2 {
        // set all elements to 0
        let mut v = elems;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == elems.len(),
                2 <= v.len() <= 200000,
                forall|j: int| 0 <= j < i ==> v[j] == 0i64,
                forall|j: int| i <= j < v.len() as int ==> #[trigger] v[j] == elems[j],
            decreases v.len() - i,
        {
            v.set(i, 0);
            i += 1;
        }
        v
    } else if mutation_kind == 3 && elems.len() < 200000 {
        // grow by one element (push 0)
        let mut v = elems;
        v.push(0);
        v
    } else if mutation_kind == 4 && elems.len() > 2 {
        // shrink by one element
        let mut v = elems;
        v.pop();
        v
    } else if mutation_kind == 5 {
        // set last element to 0
        let mut v = elems;
        let last = v.len() - 1;
        v.set(last, 0);
        v
    } else if mutation_kind == 6 {
        // set first element to max value
        let mut v = elems;
        v.set(0, 1000000000);
        v
    } else if mutation_kind == 7 {
        // nudge first element: if > 0, decrement by 1
        let mut v = elems;
        if v[0] > 0 {
            v.set(0, v[0] - 1);
        }
        v
    } else {
        elems // fallback
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
        let ans = Solution::min_operations(a.clone());
        s.push_str(&format!("{}\n", ans));
    }
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1705);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let examples: Vec<TC> = vec![
        vec![2, 0, 0],
        vec![0, 2, 0, 2, 0],
        vec![2, 0, 3, 0, 4, 6],
        vec![0, 0, 0, 10],
        vec![1],
        vec![0, 0, 0, 0, 0],
        vec![1000000000, 1000000000],
        vec![1, 0, 1],
        vec![5, 5, 5],
    ];

    for ex in &examples {
        if count >= target { break; }
        let cases = vec![ex.clone()];
        let cases: Vec<_> = cases.iter().cloned().map(generate_test_case).collect();
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }

    while count < target {
        let t: usize = if count < 20 { rng.gen_range_usize(1, 5) } else { rng.gen_range_usize(2, 20) };
        let mut cases: Vec<TC> = Vec::new();
        for _ in 0..t {
            let n = match rng.gen_range_usize(0, 4) {
                0 => rng.gen_range_usize(1, 5),
                1 => rng.gen_range_usize(2, 20),
                2 => rng.gen_range_usize(20, 200),
                3 => rng.gen_range_usize(2, 50),
                _ => rng.gen_range_usize(2, 100),
            };
            let max_v = match rng.gen_range_usize(0, 3) {
                0 => 5i64,
                1 => 100i64,
                2 => 10000i64,
                _ => 1000000000i64,
            };
            let a: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(0, max_v)).collect();
            cases.push(a);
        }
        let cases: Vec<_> = cases.iter().cloned().map(generate_test_case).collect();
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}
