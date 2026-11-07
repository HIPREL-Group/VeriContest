use vstd::prelude::*;

verus! {

pub fn generate_test_case(elements: Vec<i64>, mutation_kind: u8) -> (result: (usize, Vec<i64>))
    requires
        1 <= elements.len() <= 200000,
        forall|i: int| 0 <= i && i < elements.len() ==> 1 <= #[trigger] elements[i] && elements[i] <= 1000000000,
    ensures
        1 <= result.0 && result.0 <= 200000,
        result.1.len() == result.0,
        forall|i: int| 0 <= i && i < result.0 ==> 1 <= #[trigger] result.1@[i] && result.1@[i] <= 1000000000,
{
    if mutation_kind == 0 {
        // identity
        let n = elements.len();
        (n, elements)
    } else if mutation_kind == 1 {
        // set last element to 1 (boundary low)
        let mut a = elements;
        let last = a.len() - 1;
        a.set(last, 1);
        let n = a.len();
        (n, a)
    } else if mutation_kind == 2 {
        // set last element to 1000000000 (boundary high)
        let mut a = elements;
        let last = a.len() - 1;
        a.set(last, 1000000000);
        let n = a.len();
        (n, a)
    } else if mutation_kind == 3 {
        // set first element to 1
        let mut a = elements;
        a.set(0, 1);
        let n = a.len();
        (n, a)
    } else if mutation_kind == 4 {
        // set first element to 1000000000
        let mut a = elements;
        a.set(0, 1000000000);
        let n = a.len();
        (n, a)
    } else if mutation_kind == 5 && elements.len() < 200000 {
        // grow by one element (push 1)
        let mut a = elements;
        a.push(1);
        let n = a.len();
        (n, a)
    } else if mutation_kind == 6 && elements.len() > 1 {
        // shrink by one element (pop)
        let mut a = elements;
        a.pop();
        let n = a.len();
        (n, a)
    } else if mutation_kind == 7 {
        // nudge last element up (if < 1000000000)
        let mut a = elements;
        let last = a.len() - 1;
        if a[last] < 1000000000 {
            a.set(last, a[last] + 1);
        }
        let n = a.len();
        (n, a)
    } else if mutation_kind == 8 {
        // nudge last element down (if > 1)
        let mut a = elements;
        let last = a.len() - 1;
        if a[last] > 1 {
            a.set(last, a[last] - 1);
        }
        let n = a.len();
        (n, a)
    } else if mutation_kind == 9 {
        // set all elements to 1
        let mut a = elements;
        let ghost old_len = a.len();
        let mut j: usize = 0;
        while j < a.len()
            invariant
                0 <= j <= a.len(),
                a.len() == old_len,
                1 <= a.len() <= 200000,
                forall|k: int| 0 <= k && k < j ==> a[k] == 1i64,
                forall|k: int| j <= k && k < a.len() as int ==> a[k] == elements[k],
            decreases a.len() - j,
        {
            a.set(j, 1);
            j += 1;
        }
        let n = a.len();
        (n, a)
    } else if mutation_kind == 10 {
        // set all elements to 1000000000
        let mut a = elements;
        let ghost old_len = a.len();
        let mut j: usize = 0;
        while j < a.len()
            invariant
                0 <= j <= a.len(),
                a.len() == old_len,
                1 <= a.len() <= 200000,
                forall|k: int| 0 <= k && k < j ==> a[k] == 1000000000i64,
                forall|k: int| j <= k && k < a.len() as int ==> a[k] == elements[k],
            decreases a.len() - j,
        {
            a.set(j, 1000000000);
            j += 1;
        }
        let n = a.len();
        (n, a)
    } else {
        // fallback: identity
        let n = elements.len();
        (n, elements)
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
        let n = a.len();
        let count = Solution::is_valley(n, a.clone());
        s.push_str(if count == 1 { "YES\n" } else { "NO\n" });
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
        vec![3, 2, 2, 1, 2, 2, 3],
        vec![1, 1, 1, 2, 3, 3, 4, 5, 6, 6, 6],
        vec![1, 2, 3, 4, 3, 2, 1],
        vec![1],
        vec![5, 5, 5],
        vec![1, 2],
        vec![2, 1],
        vec![3, 1, 4, 1, 5],  // multiple valleys
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
                0 => rng.gen_range_usize(1, 5),
                1 => rng.gen_range_usize(2, 30),
                2 => rng.gen_range_usize(50, 200),
                _ => rng.gen_range_usize(2, 100),
            };
            cases.push(random_a(&mut rng, n, 5));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

