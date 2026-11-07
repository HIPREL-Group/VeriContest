use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    a_vals: Vec<i32>,
    b_vals: Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= a_vals.len() <= 100,
        a_vals.len() == b_vals.len(),
        forall|i: int| 0 <= i < a_vals.len() ==> -100 <= #[trigger] a_vals[i] <= 100,
        forall|i: int| 0 <= i < b_vals.len() ==> -100 <= #[trigger] b_vals[i] <= 100,
    ensures
        1 <= result.0.len() <= 100,
        result.0.len() == result.1.len(),
        forall|i: int| 0 <= i < result.0.len() ==> -100 <= #[trigger] result.0[i] <= 100,
        forall|i: int| 0 <= i < result.1.len() ==> -100 <= #[trigger] result.1[i] <= 100,
{
    if mutation_kind == 0 {
        // identity
        (a_vals, b_vals)
    } else if mutation_kind == 1 {
        // set all elements of a to 0
        let mut a = a_vals;
        let n = a.len();
        let mut i: usize = 0;
        while i < n
            invariant
                n == a.len(),
                n == a_vals.len(),
                0 <= i <= n,
                1 <= n <= 100,
                forall|j: int| 0 <= j < i ==> a[j] == 0i32,
                forall|j: int| i <= j < n ==> a[j] == a_vals[j],
            decreases n - i,
        {
            a.set(i, 0);
            i += 1;
        }
        (a, b_vals)
    } else if mutation_kind == 2 {
        // set all elements of b to 0
        let mut b = b_vals;
        let n = b.len();
        let mut i: usize = 0;
        while i < n
            invariant
                n == b.len(),
                n == b_vals.len(),
                0 <= i <= n,
                1 <= n <= 100,
                forall|j: int| 0 <= j < i ==> b[j] == 0i32,
                forall|j: int| i <= j < n ==> b[j] == b_vals[j],
            decreases n - i,
        {
            b.set(i, 0);
            i += 1;
        }
        (a_vals, b)
    } else if mutation_kind == 3 {
        // nudge first element of a by +1 (if in range)
        let mut a = a_vals;
        if a[0] < 100 {
            a.set(0, a[0] + 1);
        }
        (a, b_vals)
    } else if mutation_kind == 4 {
        // nudge first element of b by -1 (if in range)
        let mut b = b_vals;
        if b[0] > -100 {
            b.set(0, b[0] - 1);
        }
        (a_vals, b)
    } else if mutation_kind == 5 {
        // copy b into a (transformation tests identity)
        let mut a = a_vals;
        let n = a.len();
        let mut i: usize = 0;
        while i < n
            invariant
                n == a.len(),
                n == a_vals.len(),
                n == b_vals.len(),
                0 <= i <= n,
                1 <= n <= 100,
                forall|j: int| 0 <= j < i ==> a[j] == b_vals[j],
                forall|j: int| i <= j < n ==> a[j] == a_vals[j],
                forall|j: int| 0 <= j < b_vals.len() ==> -100 <= #[trigger] b_vals[j] <= 100,
            decreases n - i,
        {
            a.set(i, b_vals[i]);
            i += 1;
        }
        (a, b_vals)
    } else if mutation_kind == 6 && a_vals.len() > 1 {
        // swap first two elements of a
        let mut a = a_vals;
        let tmp = a[0];
        a.set(0, a[1]);
        a.set(1, tmp);
        (a, b_vals)
    } else if mutation_kind == 7 {
        // set all elements of a to -100 (min boundary)
        let mut a = a_vals;
        let n = a.len();
        let mut i: usize = 0;
        while i < n
            invariant
                n == a.len(),
                n == a_vals.len(),
                0 <= i <= n,
                1 <= n <= 100,
                forall|j: int| 0 <= j < i ==> a[j] == -100i32,
                forall|j: int| i <= j < n ==> a[j] == a_vals[j],
            decreases n - i,
        {
            a.set(i, -100);
            i += 1;
        }
        (a, b_vals)
    } else if mutation_kind == 8 {
        // set all elements of b to 100 (max boundary)
        let mut b = b_vals;
        let n = b.len();
        let mut i: usize = 0;
        while i < n
            invariant
                n == b.len(),
                n == b_vals.len(),
                0 <= i <= n,
                1 <= n <= 100,
                forall|j: int| 0 <= j < i ==> b[j] == 100i32,
                forall|j: int| i <= j < n ==> b[j] == b_vals[j],
            decreases n - i,
        {
            b.set(i, 100);
            i += 1;
        }
        (a_vals, b)
    } else if mutation_kind == 9 && a_vals.len() > 1 {
        // swap first two elements of b
        let mut b = b_vals;
        let tmp = b[0];
        b.set(0, b[1]);
        b.set(1, tmp);
        (a_vals, b)
    } else {
        // fallback: identity
        (a_vals, b_vals)
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

fn build_input(cases: &[(Vec<i32>, Vec<i32>)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (a, b) in cases {
        s.push_str(&format!("{}\n", a.len()));
        let p1: Vec<String> = a.iter().map(|v| v.to_string()).collect();
        s.push_str(&p1.join(" "));
        s.push('\n');
        let p2: Vec<String> = b.iter().map(|v| v.to_string()).collect();
        s.push_str(&p2.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[bool]) -> String {
    let mut s = String::new();
    for &a in answers {
        s.push_str(if a { "YES\n" } else { "NO\n" });
    }
    s
}

fn random_array(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n { v.push(rng.gen_range_i64(-100, 100) as i32); }
    v
}

fn build_a_to_b(rng: &mut Rng, n: usize) -> (Vec<i32>, Vec<i32>) {
    // Build a, then make b by adding 0 or 1 to chosen indices and permuting
    let a = random_array(rng, n);
    let mut b = a.clone();
    // choose k random indices to add 1
    let k = rng.gen_range_usize(0, n);
    let mut indices: Vec<usize> = (0..n).collect();
    for i in (1..n).rev() {
        let j = (rng.next_u64() as usize) % (i + 1);
        indices.swap(i, j);
    }
    for idx in 0..k {
        let i = indices[idx];
        if b[i] < 100 { b[i] += 1; }
    }
    // permute b
    for i in (1..n).rev() {
        let j = (rng.next_u64() as usize) % (i + 1);
        b.swap(i, j);
    }
    (a, b)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut seen: HashSet<String> = HashSet::new();

    let emit = |cases: &[(Vec<i32>, Vec<i32>)], seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let inp = build_input(cases);
        if !seen.insert(inp.clone()) { return; }
        let answers: Vec<bool> = cases.iter().map(|(a, b)| Solution::can_transform(a.clone(), b.clone())).collect();
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // Edge cases
    let edges: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![1], vec![1]),
        (vec![1], vec![2]),
        (vec![0], vec![1]),
        (vec![0], vec![0]),
        (vec![100], vec![100]),
        (vec![-100], vec![-100]),
        (vec![-100], vec![-99]),
        (vec![-100, 100], vec![-100, 100]),
        (vec![1, 2, 3], vec![2, 3, 4]),
        (vec![1, 2, 3], vec![1, 2, 3]),
        (vec![1, 2, 3], vec![1, 2, 4]),
        (vec![1, 2, 3], vec![3, 1, 2]),
    ];
    emit(&edges, &mut seen, &mut out, &mut count);
    for ec in &edges {
        emit(&[ec.clone()], &mut seen, &mut out, &mut count);
    }

    // Random cases - mix of valid (a -> b through transformation) and arbitrary
    while count < target {
        let t: usize = if count < 5 { 1 } else { rng.gen_range_usize(1, 30) };
        let mut cases: Vec<(Vec<i32>, Vec<i32>)> = Vec::new();
        for _ in 0..t {
            let n = rng.gen_range_usize(1, 50);
            let case = if rng.next_u64() % 3 == 0 {
                // Valid pair
                build_a_to_b(&mut rng, n)
            } else {
                let a = random_array(&mut rng, n);
                let b = random_array(&mut rng, n);
                (a, b)
            };
            cases.push(case);
        }
        emit(&cases, &mut seen, &mut out, &mut count);
    }
}

