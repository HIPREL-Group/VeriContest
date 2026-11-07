use vstd::prelude::*;

verus! {

pub open spec fn spec_i2min(a: int, b: int) -> int {
    if a < b { a } else { b }
}

pub open spec fn spec_i2max(a: int, b: int) -> int {
    if a > b { a } else { b }
}

pub open spec fn spec_min_first_i(s: Seq<i64>, i: int) -> int {
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

pub open spec fn spec_max_first_i(s: Seq<i64>, i: int) -> int {
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

pub open spec fn spec_axis_span(s: Seq<i64>) -> int {
    spec_max_first_i(s, 4) - spec_min_first_i(s, 4)
}

// Build a vec with 2 copies of lo and 2 copies of hi based on a pattern
// pattern in 0..6 selects which positions get 'hi' (a 2-of-4 choice)
pub open spec fn pattern_is_hi(pattern: u8, i: int) -> bool {
    // 6 patterns: (0,1), (0,2), (0,3), (1,2), (1,3), (2,3) - positions that are hi
    if pattern == 0 {
        i == 0 || i == 1
    } else if pattern == 1 {
        i == 0 || i == 2
    } else if pattern == 2 {
        i == 0 || i == 3
    } else if pattern == 3 {
        i == 1 || i == 2
    } else if pattern == 4 {
        i == 1 || i == 3
    } else {
        i == 2 || i == 3
    }
}

pub fn build_vec(lo: i64, hi: i64, pattern: u8) -> (v: Vec<i64>)
    requires
        lo < hi,
        -1000 <= lo <= 1000,
        -1000 <= hi <= 1000,
        pattern < 6,
    ensures
        v.len() == 4,
        forall|i: int| 0 <= i < 4 ==> (#[trigger] v[i]) == (if pattern_is_hi(pattern, i) { hi } else { lo }),
        forall|i: int| 0 <= i < 4 ==> -1000 <= (#[trigger] v[i] as int) <= 1000,
{
    let mut v: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < 4
        invariant
            v.len() == i,
            i <= 4,
            lo < hi,
            -1000 <= lo <= 1000,
            -1000 <= hi <= 1000,
            pattern < 6,
            forall|k: int| 0 <= k < i as int ==> (#[trigger] v[k]) == (if pattern_is_hi(pattern, k) { hi } else { lo }),
        decreases 4 - i,
    {
        let is_hi = if pattern == 0 {
            i == 0 || i == 1
        } else if pattern == 1 {
            i == 0 || i == 2
        } else if pattern == 2 {
            i == 0 || i == 3
        } else if pattern == 3 {
            i == 1 || i == 2
        } else if pattern == 4 {
            i == 1 || i == 3
        } else {
            i == 2 || i == 3
        };
        if is_hi {
            v.push(hi);
        } else {
            v.push(lo);
        }
        i = i + 1;
    }
    v
}

// Helper: if v has 2 lo's and 2 hi's with lo<hi, then min=lo, max=hi
pub proof fn span_lemma(v: Seq<i64>, lo: i64, hi: i64, pattern: u8)
    requires
        v.len() == 4,
        lo < hi,
        pattern < 6,
        forall|i: int| 0 <= i < 4 ==> (#[trigger] v[i]) == (if pattern_is_hi(pattern, i) { hi } else { lo }),
    ensures
        spec_axis_span(v) == hi as int - lo as int,
{
    // Enumerate patterns
    assert(v[0] == lo || v[0] == hi);
    assert(v[1] == lo || v[1] == hi);
    assert(v[2] == lo || v[2] == hi);
    assert(v[3] == lo || v[3] == hi);
    // min over all 4 is lo, max is hi
    // Because each pattern has at least one lo and one hi
    if pattern == 0 {
        assert(v[2] == lo && v[0] == hi);
    } else if pattern == 1 {
        assert(v[1] == lo && v[0] == hi);
    } else if pattern == 2 {
        assert(v[1] == lo && v[0] == hi);
    } else if pattern == 3 {
        assert(v[0] == lo && v[1] == hi);
    } else if pattern == 4 {
        assert(v[0] == lo && v[1] == hi);
    } else {
        assert(v[0] == lo && v[2] == hi);
    }
}

pub fn generate_test_case(
    x_lo: i64,
    y_lo: i64,
    side: i64,
    xp: u8,
    yp: u8,
) -> (r: (Vec<i64>, Vec<i64>))
    requires
        -1000 <= x_lo <= 1000,
        -1000 <= y_lo <= 1000,
        side > 0,
        x_lo + side <= 1000,
        y_lo + side <= 1000,
        xp < 6,
        yp < 6,
    ensures
        r.0.len() == 4,
        r.1.len() == 4,
        forall|j: int|
            0 <= j < 4 ==> -1000 <= (#[trigger] r.0[j] as int) && (r.0[j] as int) <= 1000 && -1000 <= (r.1[j] as int) && (r.1[j] as int) <= 1000,
        spec_axis_span(r.0@) == spec_axis_span(r.1@),
        spec_axis_span(r.0@) > 0,
{
    let x_hi = x_lo + side;
    let y_hi = y_lo + side;
    let xs = build_vec(x_lo, x_hi, xp);
    let ys = build_vec(y_lo, y_hi, yp);
    proof {
        span_lemma(xs@, x_lo, x_hi, xp);
        span_lemma(ys@, y_lo, y_hi, yp);
    }
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

fn pick_adv(rng: &mut Rng) -> Case {
    let mode = rng.next_u64() % 5;
    let (x0, y0, side) = match mode {
        0 => (-1000, -1000, 2000), // max possible
        1 => (-1000, -1000, 1),
        2 => (999, 999, 1),
        3 => {
            let s = rng.gen_range_i64(1, 1000);
            (rng.gen_range_i64(-1000, 1000 - s), rng.gen_range_i64(-1000, 1000 - s), s)
        }
        _ => {
            // Squares right at boundary
            let s = rng.gen_range_i64(1, 2000);
            let x0 = rng.gen_range_i64(-1000, 1000 - s.min(1999));
            let y0 = rng.gen_range_i64(-1000, 1000 - s.min(1999));
            (x0, y0, s.min(1000))
        }
    };
    let mut corners = vec![(x0, y0), (x0 + side, y0), (x0, y0 + side), (x0 + side, y0 + side)];
    for i in (1..4).rev() {
        let j = (rng.next_u64() as usize) % (i + 1);
        corners.swap(i, j);
    }
    let xs: Vec<i64> = corners.iter().map(|&(x, _)| x).collect();
    let ys: Vec<i64> = corners.iter().map(|&(_, y)| y).collect();
    (xs, ys)
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(31415);
    let mut seen: HashSet<String> = HashSet::new();

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    while count < target {
        let t: usize = if count < 30 { rng.gen_range_usize(10, 30) } else { rng.gen_range_usize(20, 100) };
        let mut cases: Vec<Case> = Vec::new();
        for _ in 0..t {
            cases.push(pick_adv(&mut rng));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i64> = cases.iter().map(|c| solve(c)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

