use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<i32>, mutation_kind: u8) -> (result: (usize, Vec<i32>))
    requires
        2 <= values.len() <= 1000,
        forall|i: int| 0 <= i < values.len() ==> #[trigger] values[i] == 1 || values[i] == 2,
    ensures
        2 <= result.0 <= 1000,
        result.0 == result.1.len(),
        forall|i: int| 0 <= i < result.0 as int ==> #[trigger] result.1[i] == 1 || result.1[i] == 2,
{
    if mutation_kind == 0 {
        // identity
        let n = values.len();
        (n, values)
    } else if mutation_kind == 1 {
        // set first element to 1
        let mut v = values;
        v.set(0, 1);
        let n = v.len();
        (n, v)
    } else if mutation_kind == 2 {
        // set first element to 2
        let mut v = values;
        v.set(0, 2);
        let n = v.len();
        (n, v)
    } else if mutation_kind == 3 {
        // set last element to 1
        let mut v = values;
        let last = v.len() - 1;
        v.set(last, 1);
        let n = v.len();
        (n, v)
    } else if mutation_kind == 4 {
        // set last element to 2
        let mut v = values;
        let last = v.len() - 1;
        v.set(last, 2);
        let n = v.len();
        (n, v)
    } else if mutation_kind == 5 {
        // set all elements to 1
        let len = values.len();
        let mut v = values;
        let mut i: usize = 0;
        while i < len
            invariant
                0 <= i <= len,
                v.len() == len,
                2 <= len <= 1000,
                forall|j: int| 0 <= j < i as int ==> #[trigger] v[j] == 1,
                forall|j: int| i as int <= j < len as int ==> #[trigger] v[j] == 1 || v[j] == 2,
            decreases len - i,
        {
            v.set(i, 1);
            i += 1;
        }
        (len, v)
    } else if mutation_kind == 6 {
        // set all elements to 2
        let len = values.len();
        let mut v = values;
        let mut i: usize = 0;
        while i < len
            invariant
                0 <= i <= len,
                v.len() == len,
                2 <= len <= 1000,
                forall|j: int| 0 <= j < i as int ==> #[trigger] v[j] == 2,
                forall|j: int| i as int <= j < len as int ==> #[trigger] v[j] == 1 || v[j] == 2,
            decreases len - i,
        {
            v.set(i, 2);
            i += 1;
        }
        (len, v)
    } else if mutation_kind == 7 && values.len() < 1000 {
        // grow by one element (push 1)
        let mut v = values;
        v.push(1);
        let n = v.len();
        (n, v)
    } else if mutation_kind == 8 && values.len() < 1000 {
        // grow by one element (push 2)
        let mut v = values;
        v.push(2);
        let n = v.len();
        (n, v)
    } else if mutation_kind == 9 && values.len() > 2 {
        // shrink by one element (pop)
        let mut v = values;
        v.pop();
        let n = v.len();
        (n, v)
    } else if mutation_kind == 10 && values.len() >= 2 {
        // swap first two elements
        let mut v = values;
        let a = v[0];
        let b = v[1];
        v.set(0, b);
        v.set(1, a);
        let n = v.len();
        (n, v)
    } else {
        // fallback: identity
        let n = values.len();
        (n, values)
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
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let r = (hi as i64 - lo as i64 + 1) as u64;
        (lo as i64 + (self.next_u64() % r) as i64) as i32
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

type TC = Vec<i32>;

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
        let ans = Solution::one_and_two(a.len(), a.clone());
        s.push_str(&format!("{}\n", ans));
    }
    s
}

fn random_a(rng: &mut Rng, n: usize) -> Vec<i32> {
    (0..n).map(|_| rng.gen_range_i32(1, 2)).collect()
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1788);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let examples: Vec<TC> = vec![
        vec![1, 2, 2, 1],
        vec![2, 2, 1, 1],
        vec![1, 2, 1, 2],
        vec![2, 1, 2, 1],
        vec![1, 1, 1, 1],
        vec![2, 2, 2, 2],
        vec![1, 2],
        vec![2, 1],
        vec![1, 1, 2, 2, 1, 1, 2, 2],
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
                2 => rng.gen_range_usize(50, 500),
                _ => rng.gen_range_usize(2, 100),
            };
            cases.push(random_a(&mut rng, n));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

