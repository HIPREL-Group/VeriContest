use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    elems: Vec<i32>,
    mutation_kind: u8,
) -> (a: Vec<i32>)
    requires
        2 <= elems.len() <= 100000,
        forall|k: int| 0 <= k < elems.len()
            ==> -10000 <= #[trigger] elems[k] <= 10000,
        forall|k: int| 0 <= k < elems.len()
            ==> #[trigger] elems[k] != 0,
    ensures
        2 <= a.len() <= 100000,
        forall|i: int| 0 <= i < a.len() ==> -10000 <= #[trigger] a[i] <= 10000,
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] != 0,
{
    if mutation_kind == 0 {
        // identity
        elems
    } else if mutation_kind == 1 && elems.len() < 100000 {
        // grow: append element with value 1
        let mut d = elems;
        d.push(1);
        d
    } else if mutation_kind == 2 && elems.len() > 2 {
        // shrink: remove last element
        let mut d = elems;
        d.pop();
        d
    } else if mutation_kind == 3 {
        // set first element to 1 (min positive boundary)
        let mut d = elems;
        d.set(0, 1);
        d
    } else if mutation_kind == 4 {
        // set first element to -1 (max negative boundary)
        let mut d = elems;
        d.set(0, -1);
        d
    } else if mutation_kind == 5 {
        // set first element to max boundary (10000)
        let mut d = elems;
        d.set(0, 10000);
        d
    } else if mutation_kind == 6 {
        // set first element to min boundary (-10000)
        let mut d = elems;
        d.set(0, -10000);
        d
    } else if mutation_kind == 7 {
        // set last element to 1
        let mut d = elems;
        let last = d.len() - 1;
        d.set(last, 1);
        d
    } else if mutation_kind == 8 {
        // set last element to -1
        let mut d = elems;
        let last = d.len() - 1;
        d.set(last, -1);
        d
    } else if mutation_kind == 9 && elems.len() >= 2 {
        // swap first and last elements
        let mut d = elems;
        let last = d.len() - 1;
        let first_val = d[0];
        let last_val = d[last];
        d.set(0, last_val);
        d.set(last, first_val);
        d
    } else if mutation_kind == 10 {
        // negate all elements
        let mut d = elems;
        let ghost old_len = d.len();
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == old_len,
                2 <= d.len() <= 100000,
                forall|j: int| 0 <= j < i
                    ==> -10000 <= #[trigger] d[j] <= 10000,
                forall|j: int| 0 <= j < i
                    ==> #[trigger] d[j] != 0,
                forall|j: int| i <= j < d.len()
                    ==> -10000 <= #[trigger] d[j] <= 10000,
                forall|j: int| i <= j < d.len()
                    ==> #[trigger] d[j] != 0,
            decreases d.len() - i,
        {
            let v = d[i];
            d.set(i, -v);
            i += 1;
        }
        d
    } else if mutation_kind == 11 {
        // set all elements to 1
        let mut d = elems;
        let ghost old_len = d.len();
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == old_len,
                2 <= d.len() <= 100000,
                forall|j: int| 0 <= j < i ==> d[j] == 1i32,
                forall|j: int| i <= j < d.len()
                    ==> -10000 <= #[trigger] d[j] <= 10000,
                forall|j: int| i <= j < d.len()
                    ==> #[trigger] d[j] != 0,
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        d
    } else {
        // fallback: identity
        elems
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

fn mutate(elems: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    if mutation_kind == 0 { elems }
    else if mutation_kind == 1 && elems.len() < 100000 { let mut d = elems; d.push(1); d }
    else if mutation_kind == 2 && elems.len() > 2 { let mut d = elems; d.pop(); d }
    else if mutation_kind == 3 { let mut d = elems; d[0] = 1; d }
    else if mutation_kind == 4 { let mut d = elems; d[0] = -1; d }
    else if mutation_kind == 5 { let mut d = elems; d[0] = 10000; d }
    else if mutation_kind == 6 { let mut d = elems; d[0] = -10000; d }
    else if mutation_kind == 7 { let mut d = elems; let l = d.len() - 1; d[l] = 1; d }
    else if mutation_kind == 8 { let mut d = elems; let l = d.len() - 1; d[l] = -1; d }
    else if mutation_kind == 9 && elems.len() >= 2 {
        let mut d = elems;
        let last = d.len() - 1;
        let f = d[0]; let l = d[last];
        d[0] = l; d[last] = f;
        d
    }
    else if mutation_kind == 10 { elems.into_iter().map(|x| -x).collect() }
    else if mutation_kind == 11 { let n = elems.len(); vec![1; n] }
    else { elems }
}

fn random_nonzero_array(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        let mut val = rng.gen_range_i64(-10000, 10000) as i32;
        if val == 0 { val = 1; }
        v.push(val);
    }
    v
}

fn build_input(cases: &[Vec<i32>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for a in cases {
        s.push_str(&format!("{}\n", a.len()));
        let parts: Vec<String> = a.iter().map(|v| v.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[Vec<i32>]) -> String {
    let mut s = String::new();
    for b in answers {
        let parts: Vec<String> = b.iter().map(|v| v.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut seen: HashSet<String> = HashSet::new();

    let emit = |cases: &[Vec<i32>], seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let inp = build_input(cases);
        if !seen.insert(inp.clone()) { return; }
        let answers: Vec<Vec<i32>> = cases.iter().map(|a| Solution::construct_coeffs(a.clone())).collect();
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // examples bundle
    let examples: Vec<Vec<i32>> = vec![
        vec![5, 5],
        vec![5, -2, 10, -9, 4],
        vec![1, 2, 3, 4, 5, 6, 7],
    ];
    emit(&examples, &mut seen, &mut out, &mut count);
    for ex in &examples {
        emit(&[ex.clone()], &mut seen, &mut out, &mut count);
    }

    let edge_cases: Vec<Vec<i32>> = vec![
        vec![1, 1], vec![1, -1], vec![10000, 10000], vec![-10000, -10000],
        vec![10000, -10000], vec![1, 2, 3], vec![1, 1, 1, 1], vec![1, 1, 1, 1, 1],
        vec![-1, -1, -1, -1], vec![1, -1, 1, -1, 1],
    ];
    let mut buf: Vec<Vec<i32>> = Vec::new();
    let mut bundle_size: usize = 1;
    for ec in &edge_cases {
        buf.push(ec.clone());
        if buf.len() >= bundle_size {
            emit(&buf, &mut seen, &mut out, &mut count);
            buf.clear();
            bundle_size = 1 + rng.gen_range_usize(0, 10);
        }
    }
    if !buf.is_empty() { emit(&buf, &mut seen, &mut out, &mut count); buf.clear(); }

    let mutation_kinds: Vec<u8> = (0..=11).collect();
    let seed_arrays: Vec<Vec<i32>> = vec![
        vec![5, 5],
        vec![5, -2, 10, -9, 4],
        vec![1, 2, 3, 4, 5, 6, 7],
        vec![10000, -10000, 5000, -5000],
        vec![1, 1, 1],
    ];
    for sa in &seed_arrays {
        for &mk in &mutation_kinds {
            let result = mutate(sa.clone(), mk);
            buf.push(result);
            if buf.len() >= bundle_size {
                emit(&buf, &mut seen, &mut out, &mut count);
                buf.clear();
                bundle_size = 1 + rng.gen_range_usize(0, 20);
            }
        }
    }
    if !buf.is_empty() { emit(&buf, &mut seen, &mut out, &mut count); buf.clear(); }

    while count < target {
        let t: usize = if count < 5 { 1 } else { rng.gen_range_usize(1, 20) };
        let mut cases: Vec<Vec<i32>> = Vec::new();
        for _ in 0..t {
            let n: usize = match rng.gen_range_usize(0, 4) {
                0 => rng.gen_range_usize(2, 5),
                1 => rng.gen_range_usize(2, 10),
                2 => rng.gen_range_usize(11, 100),
                3 => rng.gen_range_usize(101, 1000),
                _ => rng.gen_range_usize(2, 200),
            };
            let arr = random_nonzero_array(&mut rng, n);
            cases.push(arr);
        }
        emit(&cases, &mut seen, &mut out, &mut count);
    }
}

