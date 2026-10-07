use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    raw_a: Vec<u32>,
    raw_b: Vec<u32>,
    mutation_kind: u8,
) -> (result: (Vec<u32>, Vec<u32>, usize))
    requires
        1 <= raw_a.len() <= 50,
        raw_a.len() == raw_b.len(),
        forall|i: int| 0 <= i < raw_a.len() ==> 1 <= #[trigger] raw_a[i] <= 50,
        forall|i: int| 0 <= i < raw_b.len() ==> 1 <= #[trigger] raw_b[i] <= 50,
    ensures
        1 <= result.2 <= 50,
        result.0.len() == result.2,
        result.1.len() == result.2,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 50,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 50,
        result.0[0] <= 10,
        exists|i: int| 0 <= i < result.0.len() && #[trigger] result.0[i] <= 10,
{
    let n = raw_a.len();
    let mut a = raw_a;
    let mut b = raw_b;
    // Always force a[0] = 5 to guarantee the "exists" condition (a[0] <= 10).
    a.set(0, 5u32);
    if mutation_kind == 0 {
        // identity-with-a0=5
    } else if mutation_kind == 1 {
        let mut i: usize = 1;
        while i < n
            invariant
                a.len() == n,
                b.len() == n,
                1 <= n <= 50,
                1 <= i <= n,
                a[0] == 5u32,
                forall|j: int| 1 <= j < i ==> a[j] == 1u32,
                forall|j: int| i <= j < a.len() ==> 1 <= #[trigger] a[j] <= 50,
                forall|j: int| 0 <= j < b.len() ==> 1 <= #[trigger] b[j] <= 50,
            decreases n - i,
        {
            a.set(i, 1u32);
            i += 1;
        }
    } else if mutation_kind == 2 {
        let mut i: usize = 1;
        while i < n
            invariant
                a.len() == n,
                b.len() == n,
                1 <= n <= 50,
                1 <= i <= n,
                a[0] == 5u32,
                forall|j: int| 1 <= j < i ==> a[j] == 10u32,
                forall|j: int| i <= j < a.len() ==> 1 <= #[trigger] a[j] <= 50,
                forall|j: int| 0 <= j < b.len() ==> 1 <= #[trigger] b[j] <= 50,
            decreases n - i,
        {
            a.set(i, 10u32);
            i += 1;
        }
    } else if mutation_kind == 3 {
        let mut i: usize = 0;
        while i < n
            invariant
                a.len() == n,
                b.len() == n,
                1 <= n <= 50,
                0 <= i <= n,
                a[0] == 5u32,
                forall|j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j] <= 50,
                forall|j: int| 0 <= j < i ==> b[j] == ((j + 1) as u32),
                forall|j: int| i <= j < b.len() ==> 1 <= #[trigger] b[j] <= 50,
            decreases n - i,
        {
            b.set(i, (i + 1) as u32);
            i += 1;
        }
    } else if mutation_kind == 4 {
        if n > 1 {
            a.set(n - 1, 1u32);
        }
    } else if mutation_kind == 5 {
        if n > 1 {
            a.set(n - 1, 50u32);
        }
    } else {
        // identity-with-a0=5
    }
    proof {
        assert(a[0] == 5u32);
    }
    let res = (a, b, n);
    proof {
        assert(res.0[0int] == 5u32);
        assert(res.0[0int] <= 10);
        assert(exists|i: int| 0 <= i < res.0.len() && #[trigger] res.0[i] <= 10) by {
            assert(res.0[0int] <= 10);
        }
    }
    res
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
        lo + (self.next_u64() as u32) % (hi - lo + 1)
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

fn build_input(cases: &[(Vec<u32>, Vec<u32>)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (a, b) in cases {
        s.push_str(&format!("{}\n", a.len()));
        for i in 0..a.len() {
            s.push_str(&format!("{} {}\n", a[i], b[i]));
        }
    }
    s
}

fn build_output(answers: &[usize]) -> String {
    let mut s = String::new();
    for a in answers {
        s.push_str(&format!("{}\n", a));
    }
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1850);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);

    let mut emit = |cases: Vec<(Vec<u32>, Vec<u32>)>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>| -> bool {
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { return false; }
        let mut answers: Vec<usize> = Vec::new();
        for (a, b) in &cases {
            let n = a.len();
            answers.push(Solution::find_winner(a.clone(), b.clone(), n));
        }
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        true
    };

    // Sample
    {
        let cases: Vec<(Vec<u32>, Vec<u32>)> = vec![
            (vec![7, 12, 9, 9, 10], vec![2, 5, 3, 4, 1]),
            (vec![1, 3, 4, 11], vec![2, 4, 6, 5]),
            (vec![1], vec![43]),
        ];
        emit(cases, &mut seen, &mut out);
    }
    let mut count = 1usize;

    while count < target {
        let t = rng.gen_range_usize(1, 5);
        let mut cases: Vec<(Vec<u32>, Vec<u32>)> = Vec::new();
        for _ in 0..t {
            let n = rng.gen_range_usize(1, 50);
            let mut a: Vec<u32> = Vec::with_capacity(n);
            let mut b_used: HashSet<u32> = HashSet::new();
            let mut b_vec: Vec<u32> = Vec::with_capacity(n);
            for _ in 0..n {
                a.push(rng.gen_range_u32(1, 50));
                let mut bv = rng.gen_range_u32(1, 50);
                while b_used.contains(&bv) {
                    bv = rng.gen_range_u32(1, 50);
                }
                b_used.insert(bv);
                b_vec.push(bv);
            }
            // Ensure at least one a_i <= 10
            let mut has_small = false;
            for &x in &a {
                if x <= 10 { has_small = true; break; }
            }
            if !has_small {
                let idx = rng.gen_range_usize(0, n - 1);
                a[idx] = rng.gen_range_u32(1, 10);
            }
            cases.push((a, b_vec));
        }
        if emit(cases, &mut seen, &mut out) {
            count += 1;
        }
    }
}
