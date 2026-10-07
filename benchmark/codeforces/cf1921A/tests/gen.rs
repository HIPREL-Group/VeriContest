use vstd::prelude::*;

verus! {

pub open spec fn spec_i2min(a: int, b: int) -> int {
    if a < b { a } else { b }
}

pub open spec fn spec_i2max(a: int, b: int) -> int {
    if a > b { a } else { b }
}

pub open spec fn spec_min_first_i(s: Seq<i64>, i: int) -> int
    recommends
        s.len() == 4,
        1 <= i <= 4,
{
    if i == 1 {
        s[0] as int
    } else if i == 2 {
        spec_i2min(s[0] as int, s[1] as int)
    } else if i == 3 {
        spec_i2min(spec_i2min(s[0] as int, s[1] as int), s[2] as int)
    } else {
        spec_i2min(
            spec_i2min(s[0] as int, s[1] as int),
            spec_i2min(s[2] as int, s[3] as int),
        )
    }
}

pub open spec fn spec_max_first_i(s: Seq<i64>, i: int) -> int
    recommends
        s.len() == 4,
        1 <= i <= 4,
{
    if i == 1 {
        s[0] as int
    } else if i == 2 {
        spec_i2max(s[0] as int, s[1] as int)
    } else if i == 3 {
        spec_i2max(spec_i2max(s[0] as int, s[1] as int), s[2] as int)
    } else {
        spec_i2max(
            spec_i2max(s[0] as int, s[1] as int),
            spec_i2max(s[2] as int, s[3] as int),
        )
    }
}

pub open spec fn spec_axis_span(s: Seq<i64>) -> int
    recommends
        s.len() == 4,
{
    spec_max_first_i(s, 4) - spec_min_first_i(s, 4)
}

// Helper lemma: for a vector [lo, lo, hi, hi] with hi > lo, span = hi - lo
proof fn lemma_axis_span_pair(s: Seq<i64>, lo: i64, hi: i64)
    requires
        s.len() == 4,
        s[0] == lo,
        s[1] == lo,
        s[2] == hi,
        s[3] == hi,
        hi > lo,
    ensures
        spec_axis_span(s) == (hi - lo) as int,
{
    // Expand spec_min_first_i(s, 4)
    assert(spec_i2min(s[0] as int, s[1] as int) == lo as int);
    assert(spec_i2min(s[2] as int, s[3] as int) == hi as int);
    assert(spec_i2min(lo as int, hi as int) == lo as int);
    assert(spec_min_first_i(s, 4) == lo as int);

    // Expand spec_max_first_i(s, 4)
    assert(spec_i2max(s[0] as int, s[1] as int) == lo as int);
    assert(spec_i2max(s[2] as int, s[3] as int) == hi as int);
    assert(spec_i2max(lo as int, hi as int) == hi as int);
    assert(spec_max_first_i(s, 4) == hi as int);

    assert(spec_axis_span(s) == (hi - lo) as int);
}

// Helper lemma: for a vector [hi, lo, hi, lo] with hi > lo, span = hi - lo
proof fn lemma_axis_span_alt(s: Seq<i64>, lo: i64, hi: i64)
    requires
        s.len() == 4,
        s[0] == hi,
        s[1] == lo,
        s[2] == hi,
        s[3] == lo,
        hi > lo,
    ensures
        spec_axis_span(s) == (hi - lo) as int,
{
    assert(spec_i2min(s[0] as int, s[1] as int) == lo as int);
    assert(spec_i2min(s[2] as int, s[3] as int) == lo as int);
    assert(spec_i2min(lo as int, lo as int) == lo as int);
    assert(spec_min_first_i(s, 4) == lo as int);

    assert(spec_i2max(s[0] as int, s[1] as int) == hi as int);
    assert(spec_i2max(s[2] as int, s[3] as int) == hi as int);
    assert(spec_i2max(hi as int, hi as int) == hi as int);
    assert(spec_max_first_i(s, 4) == hi as int);

    assert(spec_axis_span(s) == (hi - lo) as int);
}

// Helper lemma: for a vector [lo, hi, lo, hi] with hi > lo, span = hi - lo
proof fn lemma_axis_span_interleaved(s: Seq<i64>, lo: i64, hi: i64)
    requires
        s.len() == 4,
        s[0] == lo,
        s[1] == hi,
        s[2] == lo,
        s[3] == hi,
        hi > lo,
    ensures
        spec_axis_span(s) == (hi - lo) as int,
{
    assert(spec_i2min(s[0] as int, s[1] as int) == lo as int);
    assert(spec_i2min(s[2] as int, s[3] as int) == lo as int);
    assert(spec_i2min(lo as int, lo as int) == lo as int);
    assert(spec_min_first_i(s, 4) == lo as int);

    assert(spec_i2max(s[0] as int, s[1] as int) == hi as int);
    assert(spec_i2max(s[2] as int, s[3] as int) == hi as int);
    assert(spec_i2max(hi as int, hi as int) == hi as int);
    assert(spec_max_first_i(s, 4) == hi as int);

    assert(spec_axis_span(s) == (hi - lo) as int);
}

// Helper lemma: for a vector [hi, hi, lo, lo] with hi > lo, span = hi - lo
proof fn lemma_axis_span_reversed(s: Seq<i64>, lo: i64, hi: i64)
    requires
        s.len() == 4,
        s[0] == hi,
        s[1] == hi,
        s[2] == lo,
        s[3] == lo,
        hi > lo,
    ensures
        spec_axis_span(s) == (hi - lo) as int,
{
    assert(spec_i2min(s[0] as int, s[1] as int) == hi as int);
    assert(spec_i2min(s[2] as int, s[3] as int) == lo as int);
    assert(spec_i2min(hi as int, lo as int) == lo as int);
    assert(spec_min_first_i(s, 4) == lo as int);

    assert(spec_i2max(s[0] as int, s[1] as int) == hi as int);
    assert(spec_i2max(s[2] as int, s[3] as int) == lo as int);
    assert(spec_i2max(hi as int, lo as int) == hi as int);
    assert(spec_max_first_i(s, 4) == hi as int);

    assert(spec_axis_span(s) == (hi - lo) as int);
}

pub fn generate_test_case(
    x_lo: i64,
    y_lo: i64,
    side: i64,
    mutation_kind: u8,
) -> (result: (Vec<i64>, Vec<i64>))
    requires
        -1000 <= x_lo,
        -1000 <= y_lo,
        1 <= side,
        x_lo + side <= 1000,
        y_lo + side <= 1000,
    ensures
        result.0.len() == 4,
        result.1.len() == 4,
        forall|j: int|
            0 <= j < 4 ==> -1000 <= (#[trigger] result.0[j] as int) && (result.0[j] as int) <= 1000 && -1000 <= (result.1[j] as int) && (result.1[j] as int) <= 1000,
        spec_axis_span(result.0@) == spec_axis_span(result.1@),
        spec_axis_span(result.0@) > 0,
{
    let x_hi: i64 = x_lo + side;
    let y_hi: i64 = y_lo + side;

    let mut xs: Vec<i64> = Vec::new();
    let mut ys: Vec<i64> = Vec::new();

    if mutation_kind == 1 {
        // Reversed ordering: [x_hi, x_hi, x_lo, x_lo]
        xs.push(x_hi); xs.push(x_hi); xs.push(x_lo); xs.push(x_lo);
        ys.push(y_hi); ys.push(y_hi); ys.push(y_lo); ys.push(y_lo);

        proof {
            lemma_axis_span_reversed(xs@, x_lo, x_hi);
            lemma_axis_span_reversed(ys@, y_lo, y_hi);
        }
    } else if mutation_kind == 2 {
        // Interleaved: [x_lo, x_hi, x_lo, x_hi]
        xs.push(x_lo); xs.push(x_hi); xs.push(x_lo); xs.push(x_hi);
        ys.push(y_lo); ys.push(y_hi); ys.push(y_lo); ys.push(y_hi);

        proof {
            lemma_axis_span_interleaved(xs@, x_lo, x_hi);
            lemma_axis_span_interleaved(ys@, y_lo, y_hi);
        }
    } else if mutation_kind == 3 {
        // Alternating: [x_hi, x_lo, x_hi, x_lo]
        xs.push(x_hi); xs.push(x_lo); xs.push(x_hi); xs.push(x_lo);
        ys.push(y_hi); ys.push(y_lo); ys.push(y_hi); ys.push(y_lo);

        proof {
            lemma_axis_span_alt(xs@, x_lo, x_hi);
            lemma_axis_span_alt(ys@, y_lo, y_hi);
        }
    } else {
        // Default ordering: [x_lo, x_lo, x_hi, x_hi]
        xs.push(x_lo); xs.push(x_lo); xs.push(x_hi); xs.push(x_hi);
        ys.push(y_lo); ys.push(y_lo); ys.push(y_hi); ys.push(y_hi);

        proof {
            lemma_axis_span_pair(xs@, x_lo, x_hi);
            lemma_axis_span_pair(ys@, y_lo, y_hi);
        }
    }

    assert(xs.len() == 4);
    assert(ys.len() == 4);

    (xs, ys)
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

// Each case: 4 corners as (xs, ys)
type Case = (Vec<i64>, Vec<i64>);

fn build_input(cases: &[Case]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (xs, ys) in cases {
        for i in 0..4 {
            s.push_str(&format!("{} {}\n", xs[i], ys[i]));
        }
    }
    s
}

fn build_output(answers: &[i64]) -> String {
    let mut s = String::new();
    for a in answers { s.push_str(&format!("{}\n", a)); }
    s
}

fn solve(c: &Case) -> i64 {
    Solution::axis_aligned_square_area(c.0.clone(), c.1.clone())
}

// Generate a random axis-aligned square
fn random_square(rng: &mut Rng) -> Case {
    let side_max = rng.gen_range_i64(1, 999);
    let side = side_max;
    let x0 = rng.gen_range_i64(-1000, 1000 - side);
    let y0 = rng.gen_range_i64(-1000, 1000 - side);
    // Four corners (in random order)
    let mut corners = vec![(x0, y0), (x0 + side, y0), (x0, y0 + side), (x0 + side, y0 + side)];
    // Shuffle
    for i in (1..4).rev() {
        let j = (rng.next_u64() as usize) % (i + 1);
        corners.swap(i, j);
    }
    let xs: Vec<i64> = corners.iter().map(|&(x, _)| x).collect();
    let ys: Vec<i64> = corners.iter().map(|&(_, y)| y).collect();
    (xs, ys)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1921);
    let mut seen: HashSet<String> = HashSet::new();

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // Example
    let example: Vec<Case> = vec![
        (vec![1, 4, 1, 4], vec![2, 5, 5, 2]),
        (vec![1, -1, 1, -1], vec![1, 1, -1, -1]),
        (vec![45, 45, 17, 17], vec![11, 39, 39, 11]),
    ];
    {
        let inp = build_input(&example);
        let answers: Vec<i64> = example.iter().map(|c| solve(c)).collect();
        let outs = build_output(&answers);
        if seen.insert(inp.clone()) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
            count += 1;
        }
    }

    while count < target {
        let t: usize = if count < 30 { rng.gen_range_usize(2, 6) } else { rng.gen_range_usize(3, 20) };
        let mut cases: Vec<Case> = Vec::new();
        for _ in 0..t {
            cases.push(random_square(&mut rng));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i64> = cases.iter().map(|c| solve(c)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

