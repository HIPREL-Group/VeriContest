use vstd::prelude::*;

verus! {

// Construction: takes a Vec of 0/1 values and a mutation_kind, returns a valid Vec.
// The input `bits` must already satisfy the spec's requires so that identity
// and element-level mutations can preserve the invariant easily.
pub fn generate_test_case(bits: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= bits.len() <= 100,
        forall|k: int| 0 <= k < bits.len() ==> (#[trigger] bits[k] == 0 || bits[k] == 1),
    ensures
        1 <= result.len() <= 100,
        forall|k: int| 0 <= k < result.len() ==> (#[trigger] result[k] == 0 || result[k] == 1),
{
    if mutation_kind == 0 {
        // identity
        bits
    } else if mutation_kind == 1 {
        // flip first element
        let mut d = bits;
        let val = if d[0] == 0 { 1i32 } else { 0i32 };
        d.set(0, val);
        d
    } else if mutation_kind == 2 {
        // flip last element
        let mut d = bits;
        let last = d.len() - 1;
        let val = if d[last] == 0 { 1i32 } else { 0i32 };
        d.set(last, val);
        d
    } else if mutation_kind == 3 {
        // set all to 0
        let mut d = bits;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == bits.len(),
                1 <= d.len() <= 100,
                forall|j: int| 0 <= j < i ==> d[j] == 0,
                forall|j: int| i <= j < d.len() ==> (#[trigger] d[j] == 0 || d[j] == 1),
            decreases d.len() - i,
        {
            d.set(i, 0);
            i += 1;
        }
        d
    } else if mutation_kind == 4 {
        // set all to 1
        let mut d = bits;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == bits.len(),
                1 <= d.len() <= 100,
                forall|j: int| 0 <= j < i ==> d[j] == 1,
                forall|j: int| i <= j < d.len() ==> (#[trigger] d[j] == 0 || d[j] == 1),
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        d
    } else if mutation_kind == 5 && bits.len() < 100 {
        // grow by appending a 0
        let mut d = bits;
        d.push(0);
        d
    } else if mutation_kind == 6 && bits.len() < 100 {
        // grow by appending a 1
        let mut d = bits;
        d.push(1);
        d
    } else if mutation_kind == 7 && bits.len() > 1 {
        // shrink by removing last element
        let mut d = bits;
        d.pop();
        d
    } else {
        // fallback: identity
        bits
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

fn mutate(bits: Vec<i32>, mk: u8) -> Vec<i32> {
    if mk == 0 {
        bits
    } else if mk == 1 {
        let mut d = bits;
        d[0] = if d[0] == 0 { 1 } else { 0 };
        d
    } else if mk == 2 {
        let mut d = bits;
        let last = d.len() - 1;
        d[last] = if d[last] == 0 { 1 } else { 0 };
        d
    } else if mk == 3 {
        let mut d = bits;
        for i in 0..d.len() { d[i] = 0; }
        d
    } else if mk == 4 {
        let mut d = bits;
        for i in 0..d.len() { d[i] = 1; }
        d
    } else if mk == 5 && bits.len() < 100 {
        let mut d = bits;
        d.push(0);
        d
    } else if mk == 6 && bits.len() < 100 {
        let mut d = bits;
        d.push(1);
        d
    } else if mk == 7 && bits.len() > 1 {
        let mut d = bits;
        d.pop();
        d
    } else {
        bits
    }
}

fn random_bits(rng: &mut Rng, len: usize) -> Vec<i32> {
    (0..len).map(|_| rng.gen_range_usize(0, 1) as i32).collect()
}

fn build_input(bits: &[i32]) -> String {
    let mut s = format!("{}\n", bits.len());
    let parts: Vec<String> = bits.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |bits: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if bits.len() < 1 || bits.len() > 100 { return; }
        let key = format!("{:?}", bits);
        if !seen.insert(key) { return; }
        let inp = build_input(&bits);
        let ans = Solution::max_ones_after_flip(bits.clone());
        let outs = format!("{}\n", ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    let examples: Vec<Vec<i32>> = vec![
        vec![1, 0, 0, 1, 0],
        vec![1, 0, 0, 1],
    ];
    for ex in &examples {
        for mk in 0..=7u8 {
            let r = mutate(ex.clone(), mk);
            emit(r, &mut seen, &mut out, &mut count);
        }
    }

    let seeds: Vec<Vec<i32>> = vec![
        vec![0],
        vec![1],
        vec![0, 0, 0, 0, 0],
        vec![1, 1, 1, 1, 1],
        vec![0, 1, 0, 1, 0, 1],
        vec![1, 0, 1, 0, 1, 0],
        vec![0; 10],
        vec![1; 10],
    ];
    for s in &seeds {
        for mk in 0..=7u8 {
            let r = mutate(s.clone(), mk);
            emit(r, &mut seen, &mut out, &mut count);
        }
    }

    let size_classes: Vec<(usize, usize)> = vec![(1, 5), (6, 15), (16, 50), (51, 100)];
    for &(lo, hi) in &size_classes {
        for _ in 0..10 {
            let len = rng.gen_range_usize(lo, hi);
            let bits = random_bits(&mut rng, len);
            let mk = rng.gen_range_usize(0, 7) as u8;
            let r = mutate(bits, mk);
            emit(r, &mut seen, &mut out, &mut count);
        }
    }

    while count < target {
        let len = rng.gen_range_usize(1, 100);
        let bits = random_bits(&mut rng, len);
        emit(bits, &mut seen, &mut out, &mut count);
    }
}

