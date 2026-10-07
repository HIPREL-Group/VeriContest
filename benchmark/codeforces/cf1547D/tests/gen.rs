use vstd::prelude::*;

verus! {

pub fn generate_test_case(x: Vec<u32>, mutation_kind: u8) -> (result: (usize, Vec<u32>))
    requires
        1 <= x.len() <= 200000,
        forall|i: int| 0 <= i < x.len() ==> x[i] < 1073741824u32,
    ensures
        1 <= result.0 && result.0 <= 200000,
        result.1.len() == result.0,
        forall|i: int| 0 <= i && i < result.0 ==> result.1@[i] < 1073741824,
{
    if mutation_kind == 0 {
        // identity
        let n = x.len();
        (n, x)
    } else if mutation_kind == 1 {
        // set first element to 0
        let mut d = x;
        d.set(0, 0u32);
        let n = d.len();
        (n, d)
    } else if mutation_kind == 2 {
        // set all elements to 0
        let mut d = x;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == x.len(),
                1 <= d.len() <= 200000,
                forall|j: int| 0 <= j < i ==> d[j] == 0u32,
                forall|j: int| i <= j < d.len() as int ==> d[j] == x[j],
            decreases d.len() - i,
        {
            d.set(i, 0u32);
            i += 1;
        }
        let n = d.len();
        (n, d)
    } else if mutation_kind == 3 {
        // set all elements to max valid value (1073741823)
        let mut d = x;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == x.len(),
                1 <= d.len() <= 200000,
                forall|j: int| 0 <= j < i ==> d[j] == 1073741823u32,
                forall|j: int| i <= j < d.len() as int ==> d[j] == x[j],
            decreases d.len() - i,
        {
            d.set(i, 1073741823u32);
            i += 1;
        }
        let n = d.len();
        (n, d)
    } else if mutation_kind == 4 && x.len() < 200000 {
        // grow by one element (push 0)
        let mut d = x;
        d.push(0u32);
        let n = d.len();
        (n, d)
    } else if mutation_kind == 5 && x.len() > 1 {
        // shrink by one element (pop)
        let mut d = x;
        d.pop();
        let n = d.len();
        (n, d)
    } else if mutation_kind == 6 {
        // set last element to 0
        let mut d = x;
        let last = d.len() - 1;
        d.set(last, 0u32);
        let n = d.len();
        (n, d)
    } else if mutation_kind == 7 {
        // nudge last element up if possible
        let mut d = x;
        let last = d.len() - 1;
        if d[last] < 1073741823u32 {
            d.set(last, d[last] + 1u32);
        }
        let n = d.len();
        (n, d)
    } else if mutation_kind == 8 {
        // nudge last element down if > 0
        let mut d = x;
        let last = d.len() - 1;
        if d[last] > 0u32 {
            d.set(last, d[last] - 1u32);
        }
        let n = d.len();
        (n, d)
    } else {
        // fallback: identity
        let n = x.len();
        (n, x)
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
    fn gen_range_u32(&mut self, lo: u32, hi: u32) -> u32 {
        let range = (hi as u64 - lo as u64 + 1) as u64;
        lo + (self.next_u64() % range) as u32
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

fn mutate(x: Vec<u32>, mutation_kind: u8) -> (usize, Vec<u32>) {
    if mutation_kind == 0 {
        let n = x.len();
        (n, x)
    } else if mutation_kind == 1 {
        let mut d = x;
        if !d.is_empty() { d[0] = 0u32; }
        let n = d.len();
        (n, d)
    } else if mutation_kind == 2 {
        let n = x.len();
        (n, vec![0u32; n])
    } else if mutation_kind == 3 {
        let n = x.len();
        (n, vec![1073741823u32; n])
    } else if mutation_kind == 4 && x.len() < 200000 {
        let mut d = x; d.push(0u32);
        let n = d.len();
        (n, d)
    } else if mutation_kind == 5 && x.len() > 1 {
        let mut d = x; d.pop();
        let n = d.len();
        (n, d)
    } else if mutation_kind == 6 {
        let mut d = x;
        let last = d.len() - 1;
        d[last] = 0u32;
        let n = d.len();
        (n, d)
    } else if mutation_kind == 7 {
        let mut d = x;
        let last = d.len() - 1;
        if d[last] < 1073741823u32 { d[last] = d[last] + 1u32; }
        let n = d.len();
        (n, d)
    } else if mutation_kind == 8 {
        let mut d = x;
        let last = d.len() - 1;
        if d[last] > 0u32 { d[last] = d[last] - 1u32; }
        let n = d.len();
        (n, d)
    } else {
        let n = x.len();
        (n, x)
    }
}

fn build_input(cases: &[(usize, Vec<u32>)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (n, x) in cases {
        s.push_str(&format!("{}\n", n));
        let parts: Vec<String> = x.iter().map(|v| v.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[Vec<u32>]) -> String {
    let mut s = String::new();
    for y in answers {
        let parts: Vec<String> = y.iter().map(|v| v.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn random_vec(rng: &mut Rng, len: usize) -> Vec<u32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_u32(0, 1073741823));
    }
    v
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut seen: HashSet<String> = HashSet::new();

    let emit = |cases: &[(usize, Vec<u32>)], seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize, target: usize| -> bool {
        if *count >= target { return false; }
        let inp = build_input(cases);
        if !seen.insert(inp.clone()) { return false; }
        let answers: Vec<Vec<u32>> = cases.iter().map(|(n, x)| Solution::co_growing(*n, x.clone())).collect();
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
        true
    };

    // Examples from description
    let examples_input: Vec<Vec<u32>> = vec![
        vec![1, 3, 7, 15],
        vec![1, 2, 4, 8],
        vec![1, 2, 3, 4, 5],
        vec![1, 13, 15, 1],
        vec![0],
    ];
    let example_cases: Vec<(usize, Vec<u32>)> = examples_input.iter().map(|x| (x.len(), x.clone())).collect();
    emit(&example_cases, &mut seen, &mut out, &mut count, target);

    // Each example as standalone
    for ex in &examples_input {
        let cases: Vec<(usize, Vec<u32>)> = vec![(ex.len(), ex.clone())];
        emit(&cases, &mut seen, &mut out, &mut count, target);
    }

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8];
    // Boundary seeds
    let boundary_seeds: Vec<Vec<u32>> = vec![
        vec![0],
        vec![1073741823],
        vec![0, 0],
        vec![1073741823, 1073741823],
        vec![0, 1073741823],
        vec![1073741823, 0],
    ];
    let mut buf: Vec<(usize, Vec<u32>)> = Vec::new();
    let mut bundle_size: usize = 1;
    for bs in &boundary_seeds {
        for &mk in &mutation_kinds {
            let (n, x) = mutate(bs.clone(), mk);
            buf.push((n, x));
            if buf.len() >= bundle_size {
                emit(&buf, &mut seen, &mut out, &mut count, target);
                buf.clear();
                bundle_size = 1 + rng.gen_range_usize(0, 20);
            }
        }
    }
    if !buf.is_empty() { emit(&buf, &mut seen, &mut out, &mut count, target); buf.clear(); }

    while count < target {
        let t: usize = if count < 5 { 1 } else { rng.gen_range_usize(1, 30) };
        let mut cases: Vec<(usize, Vec<u32>)> = Vec::new();
        for _ in 0..t {
            let len = match rng.gen_range_usize(0, 4) {
                0 => rng.gen_range_usize(1, 5),
                1 => rng.gen_range_usize(1, 10),
                2 => rng.gen_range_usize(11, 100),
                3 => rng.gen_range_usize(101, 500),
                _ => rng.gen_range_usize(1, 200),
            };
            let x = random_vec(&mut rng, len);
            cases.push((len, x));
        }
        emit(&cases, &mut seen, &mut out, &mut count, target);
    }
}

