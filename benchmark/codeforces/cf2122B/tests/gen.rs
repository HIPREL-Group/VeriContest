use vstd::prelude::*;

verus! {

pub open spec fn spec_sum(nums: Seq<i64>, hi: int) -> int
    decreases hi + 1,
{
    if hi < 0 { 0 } else { spec_sum(nums, hi - 1) + nums[hi] as int }
}

proof fn sum_prefix_equal(a: Seq<i64>, b: Seq<i64>, hi: int)
    requires
        -1 <= hi < a.len(), hi < b.len(),
        forall|j: int| 0 <= j <= hi ==> a[j] == b[j],
    ensures spec_sum(a, hi) == spec_sum(b, hi),
    decreases hi + 1,
{
    if hi >= 0 { sum_prefix_equal(a, b, hi - 1); }
}

pub fn bounded_piles(raw: &Vec<i64>, n: usize) -> (result: Vec<i64>)
    requires 1 <= n <= 200000,
    ensures
        result.len() == n,
        forall|j: int| 0 <= j < result.len() ==> 0 <= #[trigger] result[j] <= 1000000000,
{
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 200000, 0 <= i <= n, result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> 0 <= #[trigger] result[j] <= 1000000000,
        decreases n - i,
    {
        let v = if i < raw.len() { raw[i] } else { 0 };
        result.push(if v < 0 { 0 } else if v > 1000000000 { 1000000000 } else { v });
        i += 1;
    }
    result
}

pub fn pile_total(values: &Vec<i64>) -> (result: i64)
    requires
        1 <= values.len() <= 200000,
        forall|j: int| 0 <= j < values.len() ==> 0 <= #[trigger] values[j] <= 1000000000,
    ensures
        result == spec_sum(values@, values.len() as int - 1),
        0 <= result <= values.len() * 1000000000,
{
    let mut i = 0usize;
    let mut total = 0i64;
    while i < values.len()
        invariant
            1 <= values.len() <= 200000,
            forall|j: int| 0 <= j < values.len() ==> 0 <= #[trigger] values[j] <= 1000000000,
            0 <= i <= values.len(),
            0 <= total <= i * 1000000000,
            total == spec_sum(values@, i as int - 1),
        decreases values.len() - i,
    {
        total += values[i];
        i += 1;
    }
    total
}

pub fn balanced_piles(raw: &Vec<i64>, n: usize, total: i64) -> (result: Vec<i64>)
    requires 1 <= n <= 200000, 0 <= total <= n * 1000000000,
    ensures
        result.len() == n,
        forall|j: int| 0 <= j < result.len() ==> 0 <= #[trigger] result[j] <= 1000000000,
        spec_sum(result@, n as int - 1) == total,
{
    let mut result: Vec<i64> = Vec::new();
    let mut remaining = total;
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 200000, 0 <= i <= n, result.len() == i,
            0 <= remaining <= (n - i) * 1000000000,
            spec_sum(result@, i as int - 1) + remaining == total,
            forall|j: int| 0 <= j < result.len() ==> 0 <= #[trigger] result[j] <= 1000000000,
        decreases n - i,
    {
        let capacity = (n - i - 1) as i64 * 1000000000;
        let low = if remaining > capacity { remaining - capacity } else { 0 };
        let high = if remaining > 1000000000 { 1000000000 } else { remaining };
        let v = if i < raw.len() { raw[i] } else { 0 };
        let v = if v < low { low } else if v > high { high } else { v };
        let ghost before = result@;
        result.push(v);
        proof { sum_prefix_equal(before, result@, i as int - 1); }
        remaining -= v;
        i += 1;
    }
    result
}

pub fn generate_test_case(raw_a: Vec<i64>, raw_b: Vec<i64>, raw_c: Vec<i64>, raw_d: Vec<i64>)
    -> (result: (Vec<i64>, Vec<i64>, Vec<i64>, Vec<i64>))
    ensures
        1 <= result.0.len() <= 200000,
        result.0.len() == result.1.len(),
        result.0.len() == result.2.len(),
        result.0.len() == result.3.len(),
        forall|j: int| 0 <= j < result.0.len() ==> 0 <= #[trigger] result.0[j] <= 1000000000,
        forall|j: int| 0 <= j < result.1.len() ==> 0 <= #[trigger] result.1[j] <= 1000000000,
        forall|j: int| 0 <= j < result.2.len() ==> 0 <= #[trigger] result.2[j] <= 1000000000,
        forall|j: int| 0 <= j < result.3.len() ==> 0 <= #[trigger] result.3[j] <= 1000000000,
        spec_sum(result.0@, result.0.len() as int - 1) == spec_sum(result.2@, result.0.len() as int - 1),
        spec_sum(result.1@, result.0.len() as int - 1) == spec_sum(result.3@, result.0.len() as int - 1),
{
    let n = if raw_a.len() == 0 { 1usize } else if raw_a.len() > 200000 { 200000usize } else { raw_a.len() };
    let a = bounded_piles(&raw_a, n);
    let b = bounded_piles(&raw_b, n);
    let sa = pile_total(&a);
    let sb = pile_total(&b);
    let c = balanced_piles(&raw_c, n, sa);
    let d = balanced_piles(&raw_d, n, sb);
    (a, b, c, d)
}


pub fn generate_candidate(
    a: Vec<i64>,
    b: Vec<i64>,
    c: Vec<i64>,
    d: Vec<i64>,
    mutation_kind: u8,
) -> (result: (Vec<i64>, Vec<i64>, Vec<i64>, Vec<i64>))
    requires
        a.len() == b.len(),
        a.len() == c.len(),
        a.len() == d.len(),
        1 <= a.len() <= 200_000,
        forall|j: int| 0 <= j < a.len() ==> 0 <= #[trigger] a[j] && a[j] <= 1_000_000_000,
        forall|j: int| 0 <= j < b.len() ==> 0 <= #[trigger] b[j] && b[j] <= 1_000_000_000,
        forall|j: int| 0 <= j < c.len() ==> 0 <= #[trigger] c[j] && c[j] <= 1_000_000_000,
        forall|j: int| 0 <= j < d.len() ==> 0 <= #[trigger] d[j] && d[j] <= 1_000_000_000,
    ensures
        1 <= result.0.len() <= 200_000,
        result.0.len() == result.1.len(),
        result.0.len() == result.2.len(),
        result.0.len() == result.3.len(),
        forall|j: int|
            #![trigger result.0[j]]
            0 <= j && j < result.0.len() ==> 0 <= #[trigger] result.0[j] && result.0[j] <= 1_000_000_000,
        forall|j: int|
            #![trigger result.1[j]]
            0 <= j && j < result.1.len() ==> 0 <= #[trigger] result.1[j] && result.1[j] <= 1_000_000_000,
        forall|j: int|
            #![trigger result.2[j]]
            0 <= j && j < result.2.len() ==> 0 <= #[trigger] result.2[j] && result.2[j] <= 1_000_000_000,
        forall|j: int|
            #![trigger result.3[j]]
            0 <= j && j < result.3.len() ==> 0 <= #[trigger] result.3[j] && result.3[j] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        (a, b, c, d)
    } else if mutation_kind == 1 {
        // set last element of a to 0
        let mut ra = a;
        let last = ra.len() - 1;
        ra.set(last, 0);
        (ra, b, c, d)
    } else if mutation_kind == 2 {
        // set last element of a to 1_000_000_000
        let mut ra = a;
        let last = ra.len() - 1;
        ra.set(last, 1_000_000_000);
        (ra, b, c, d)
    } else if mutation_kind == 3 {
        // set last element of c to 0
        let mut rc = c;
        let last = rc.len() - 1;
        rc.set(last, 0);
        (a, b, rc, d)
    } else if mutation_kind == 4 {
        // set last element of d to 0
        let mut rd = d;
        let last = rd.len() - 1;
        rd.set(last, 0);
        (a, b, c, rd)
    } else if mutation_kind == 5 && a[a.len() - 1] < 1_000_000_000 {
        // nudge last of a up
        let mut ra = a;
        let last = ra.len() - 1;
        ra.set(last, ra[last] + 1);
        (ra, b, c, d)
    } else if mutation_kind == 6 && b[b.len() - 1] > 0 {
        // nudge last of b down
        let mut rb = b;
        let last = rb.len() - 1;
        rb.set(last, rb[last] - 1);
        (a, rb, c, d)
    } else if mutation_kind == 7 && a.len() < 200_000 {
        // grow: push zeros
        let mut ra = a;
        let mut rb = b;
        let mut rc = c;
        let mut rd = d;
        ra.push(0);
        rb.push(0);
        rc.push(0);
        rd.push(0);
        (ra, rb, rc, rd)
    } else if mutation_kind == 8 && a.len() > 1 {
        // shrink: pop last
        let mut ra = a;
        let mut rb = b;
        let mut rc = c;
        let mut rd = d;
        ra.pop();
        rb.pop();
        rc.pop();
        rd.pop();
        (ra, rb, rc, rd)
    } else if mutation_kind == 9 {
        // set all a to 0
        let n = a.len();
        let mut ra = a;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                ra.len() == n,
                1 <= n <= 200_000,
                forall|j: int| 0 <= j < i ==> ra[j] == 0i64,
                forall|j: int| 0 <= j < n as int ==> 0 <= #[trigger] ra[j] && ra[j] <= 1_000_000_000i64,
            decreases n - i,
        {
            ra.set(i, 0);
            i += 1;
        }
        (ra, b, c, d)
    } else {
        // fallback: identity
        (a, b, c, d)
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

#[derive(Clone)]
struct Case {
    a: Vec<i64>,
    b: Vec<i64>,
    c: Vec<i64>,
    d: Vec<i64>,
}

fn build_input_multi(cases: &[Case]) -> String {
    let mut s = format!("{}\n", cases.len());
    for case in cases {
        s.push_str(&format!("{}\n", case.a.len()));
        for i in 0..case.a.len() {
            s.push_str(&format!("{} {} {} {}\n", case.a[i], case.b[i], case.c[i], case.d[i]));
        }
    }
    s
}

fn build_output_multi(answers: &[i64]) -> String {
    let mut s = String::new();
    for &a in answers {
        s.push_str(&format!("{}\n", a));
    }
    s
}

fn solve(c: &Case) -> i64 {
    Solution::min_pile_shuffle_operations(&c.a, &c.b, &c.c, &c.d)
}

fn random_case(rng: &mut Rng, mode: usize) -> Case {
    let n = match mode {
        0 => rng.gen_range_usize(1, 3),
        1 => rng.gen_range_usize(4, 10),
        2 => rng.gen_range_usize(11, 50),
        3 => rng.gen_range_usize(51, 200),
        _ => rng.gen_range_usize(1, 30),
    };
    let mut a = Vec::with_capacity(n);
    let mut b = Vec::with_capacity(n);
    let mut c = Vec::with_capacity(n);
    let mut d = Vec::with_capacity(n);
    let max = match mode % 3 {
        0 => 10i64,
        1 => 1000i64,
        _ => 1_000_000_000i64,
    };
    for _ in 0..n {
        // Per problem - it's guaranteed there's an op sequence transforming. We just generate any valid input.
        // The simplest: pick random a, b, c, d in range
        let av = rng.gen_range_i64(0, max);
        let bv = rng.gen_range_i64(0, max);
        let cv = rng.gen_range_i64(0, max);
        let dv = rng.gen_range_i64(0, max);
        a.push(av);
        b.push(bv);
        c.push(cv);
        d.push(dv);
    }
    Case { a, b, c, d }
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(2122);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // Examples from description
    let examples: Vec<Case> = vec![
        Case { a: vec![1, 1], b: vec![3, 1], c: vec![1, 1], d: vec![2, 1] },
        Case { a: vec![2, 0, 1], b: vec![0, 1, 1], c: vec![2, 1, 0], d: vec![2, 0, 0] },
        Case { a: vec![1, 3, 0], b: vec![2, 4, 0], c: vec![1, 3, 0], d: vec![2, 4, 0] },
    ];
    {
        let answers: Vec<i64> = examples.iter().map(|c| solve(c)).collect();
        let examples: Vec<_> = examples.iter().map(|case| {
            let (a, b, c, d) = generate_test_case(case.a.clone(), case.b.clone(), case.c.clone(), case.d.clone());
            Case { a, b, c, d }
        }).collect();
        let inp = build_input_multi(&examples);
        let outp = build_output_multi(&answers);
        if seen.insert(inp.clone()) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }

    for ex in &examples {
        if count >= target { break; }
        let cases = vec![ex.clone()];
        let answers: Vec<i64> = cases.iter().map(|c| solve(c)).collect();
        let cases: Vec<_> = cases.iter().map(|case| {
            let (a, b, c, d) = generate_test_case(case.a.clone(), case.b.clone(), case.c.clone(), case.d.clone());
            Case { a, b, c, d }
        }).collect();
        let inp = build_input_multi(&cases);
        let outp = build_output_multi(&answers);
        if seen.insert(inp.clone()) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }

    // edge cases
    let edges: Vec<Case> = vec![
        Case { a: vec![0], b: vec![0], c: vec![0], d: vec![0] },
        Case { a: vec![0], b: vec![1], c: vec![0], d: vec![1] },
        Case { a: vec![1], b: vec![0], c: vec![0], d: vec![0] },
        Case { a: vec![1, 2, 3], b: vec![1, 2, 3], c: vec![3, 2, 1], d: vec![3, 2, 1] },
        Case { a: vec![1_000_000_000], b: vec![1_000_000_000], c: vec![1_000_000_000], d: vec![1_000_000_000] },
        Case { a: vec![1_000_000_000], b: vec![0], c: vec![0], d: vec![0] },
    ];
    for chunk in edges.chunks(3) {
        if count >= target { break; }
        let cases: Vec<Case> = chunk.to_vec();
        let answers: Vec<i64> = cases.iter().map(|c| solve(c)).collect();
        let cases: Vec<_> = cases.iter().map(|case| {
            let (a, b, c, d) = generate_test_case(case.a.clone(), case.b.clone(), case.c.clone(), case.d.clone());
            Case { a, b, c, d }
        }).collect();
        let inp = build_input_multi(&cases);
        let outp = build_output_multi(&answers);
        if seen.insert(inp.clone()) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }

    while count < target {
        let t: usize = if count < 30 { rng.gen_range_usize(1, 5) } else { rng.gen_range_usize(2, 20) };
        let mut cases: Vec<Case> = Vec::with_capacity(t);
        for _ in 0..t {
            let mode = rng.gen_range_usize(0, 4);
            cases.push(random_case(&mut rng, mode));
        }
        let answers: Vec<i64> = cases.iter().map(|c| solve(c)).collect();
        let cases: Vec<_> = cases.iter().map(|case| {
            let (a, b, c, d) = generate_test_case(case.a.clone(), case.b.clone(), case.c.clone(), case.d.clone());
            Case { a, b, c, d }
        }).collect();
        let inp = build_input_multi(&cases);
        let outp = build_output_multi(&answers);
        if !seen.insert(inp.clone()) { continue; }
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
