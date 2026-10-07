use vstd::prelude::*;

verus! {

pub fn generate_test_case(raw: Vec<i64>, raw_widths: Vec<usize>, raw_heights: Vec<i64>)
    -> (result: (Vec<i64>, Vec<usize>, Vec<i64>))
    ensures valid_inputs(result.0@, result.1@, result.2@),
{
    let n = if raw.len() < 1 { 1usize } else if raw.len() > 100000 { 100000usize } else { raw.len() };
    let mut stairs: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 100000,
            0 <= i <= n,
            stairs.len() == i,
            forall|j: int| 0 <= j < stairs.len() ==> 1 <= #[trigger] stairs[j] <= 1000000000,
            forall|j: int, k: int| 0 <= j < k < stairs.len() ==> stairs[j] <= stairs[k],
        decreases n - i,
    {
        let v = if i < raw.len() { raw[i] } else { 1 };
        let mut v = if v < 1 { 1 } else if v > 1000000000 { 1000000000 } else { v };
        if i > 0 && v < stairs[i - 1] { v = stairs[i - 1]; }
        assert forall|j: int| 0 <= j < stairs.len() implies stairs[j] <= v by {
            if j < i - 1 { assert(stairs[j] <= stairs[(i - 1) as int]); }
        }
        stairs.push(v);
        i += 1;
    }
    let m = if raw_widths.len() < 1 { 1usize } else if raw_widths.len() > 100000 { 100000usize } else { raw_widths.len() };
    let mut widths: Vec<usize> = Vec::new();
    let mut heights: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i < m
        invariant
            1 <= n <= 100000,
            1 <= m <= 100000,
            0 <= i <= m,
            widths.len() == i,
            heights.len() == i,
            forall|j: int| 0 <= j < widths.len() ==> 1 <= #[trigger] widths[j] <= n,
            forall|j: int| 0 <= j < heights.len() ==> 1 <= #[trigger] heights[j] <= 1000000000,
        decreases m - i,
    {
        let w = if i < raw_widths.len() { raw_widths[i] } else { 1usize };
        let h = if i < raw_heights.len() { raw_heights[i] } else { 1i64 };
        widths.push(if w < 1 { 1 } else if w > n { n } else { w });
        heights.push(if h < 1 { 1 } else if h > 1000000000 { 1000000000 } else { h });
        i += 1;
    }
    (stairs, widths, heights)
}


// Copied from spec.rs
pub open spec fn valid_inputs(stairs: Seq<i64>, widths: Seq<usize>, heights: Seq<i64>) -> bool {
    &&& 1 <= stairs.len() <= 100_000
    &&& 1 <= widths.len() <= 100_000
    &&& widths.len() == heights.len()
    &&& forall|i: int| 0 <= i < stairs.len() ==> 1 <= #[trigger] stairs[i] <= 1_000_000_000
    &&& forall|i: int, j: int| 0 <= i < j < stairs.len() ==> stairs[i] <= stairs[j]
    &&& forall|i: int| 0 <= i < widths.len() ==> 1 <= #[trigger] (widths[i] as int) <= stairs.len()
    &&& forall|i: int| 0 <= i < heights.len() ==> 1 <= #[trigger] heights[i] <= 1_000_000_000
}

pub fn generate_candidate(
    raw_stairs: Vec<i64>,
    widths: Vec<usize>,
    heights: Vec<i64>,
    mutation_kind: u8,
) -> (result: (Vec<i64>, Vec<usize>, Vec<i64>))
    requires
        1 <= raw_stairs.len() <= 100_000,
        forall|i: int| 0 <= i < raw_stairs.len() ==> 1 <= #[trigger] raw_stairs[i] <= 1_000_000_000,
        1 <= widths.len() <= 100_000,
        widths.len() == heights.len(),
        forall|i: int| 0 <= i < widths.len() ==> 1 <= #[trigger] (widths[i] as int) <= raw_stairs.len(),
        forall|i: int| 0 <= i < heights.len() ==> 1 <= #[trigger] heights[i] <= 1_000_000_000,
    ensures
        valid_inputs(result.0@, result.1@, result.2@),
{
    let n = raw_stairs.len();

    // Build sorted stairs via prefix-max
    let mut stairs: Vec<i64> = Vec::new();
    stairs.push(raw_stairs[0]);
    let mut i: usize = 1;
    while i < n
        invariant
            1 <= i <= n,
            n == raw_stairs.len(),
            stairs.len() == i,
            1 <= n <= 100_000,
            forall|k: int| 0 <= k < raw_stairs.len() ==> 1 <= #[trigger] raw_stairs[k] <= 1_000_000_000,
            forall|k: int| 0 <= k < stairs.len() ==> 1 <= #[trigger] stairs[k] <= 1_000_000_000,
            forall|k: int, l: int| 0 <= k < l < stairs.len() ==> stairs[k] <= stairs[l],
        decreases n - i,
    {
        let prev = stairs[i - 1];
        let cur = raw_stairs[i];
        let val = if cur >= prev { cur } else { prev };
        stairs.push(val);
        proof {
            let slen = stairs@.len() as int;
            assert(stairs[slen - 1] >= stairs[slen - 2]);
            assert forall|k: int, l: int| 0 <= k < l < slen implies stairs[k] <= stairs[l] by {
                if l < slen - 1 {
                } else if k == slen - 2 {
                } else {
                    assert(stairs[k] <= stairs[slen - 2]);
                }
            };
        }
        i += 1;
    }

    if mutation_kind == 0 {
        (stairs, widths, heights)
    } else if mutation_kind == 1 {
        // Constant stairs: all equal to raw_stairs[0]
        let val = raw_stairs[0];
        let mut s: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                s.len() == j,
                n == raw_stairs.len(),
                1 <= n <= 100_000,
                1 <= val <= 1_000_000_000,
                forall|k: int| 0 <= k < s.len() ==> #[trigger] s[k] == val,
            decreases n - j,
        {
            s.push(val);
            j += 1;
        }
        proof {
            assert forall|k: int| 0 <= k < s.len() implies 1 <= #[trigger] s[k] <= 1_000_000_000 by {};
            assert forall|k: int, l: int| 0 <= k < l < s.len() implies s[k] <= s[l] by {};
        }
        (s, widths, heights)
    } else if mutation_kind == 2 {
        // All heights set to 1
        let m = heights.len();
        let mut h: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < m
            invariant
                0 <= j <= m,
                h.len() == j,
                m == widths.len(),
                1 <= m <= 100_000,
                forall|k: int| 0 <= k < h.len() ==> #[trigger] h[k] == 1i64,
            decreases m - j,
        {
            h.push(1i64);
            j += 1;
        }
        proof {
            assert forall|k: int| 0 <= k < h.len() implies 1 <= #[trigger] h[k] <= 1_000_000_000 by {};
        }
        (stairs, widths, h)
    } else if mutation_kind == 3 {
        // All widths set to 1
        let m = widths.len();
        let mut w: Vec<usize> = Vec::new();
        let mut j: usize = 0;
        while j < m
            invariant
                0 <= j <= m,
                w.len() == j,
                m == heights.len(),
                1 <= m <= 100_000,
                forall|k: int| 0 <= k < w.len() ==> #[trigger] w[k] == 1usize,
            decreases m - j,
        {
            w.push(1usize);
            j += 1;
        }
        proof {
            assert(stairs.len() >= 1);
            assert forall|k: int| 0 <= k < w.len() implies 1 <= #[trigger] (w[k] as int) <= stairs.len() by {};
        }
        (stairs, w, heights)
    } else if mutation_kind == 4 {
        // All widths set to n (max width)
        let m = widths.len();
        let sn = stairs.len();
        let mut w: Vec<usize> = Vec::new();
        let mut j: usize = 0;
        while j < m
            invariant
                0 <= j <= m,
                w.len() == j,
                m == heights.len(),
                1 <= m <= 100_000,
                sn == stairs.len(),
                1 <= sn <= 100_000,
                forall|k: int| 0 <= k < w.len() ==> #[trigger] w[k] == sn,
            decreases m - j,
        {
            w.push(sn);
            j += 1;
        }
        proof {
            assert forall|k: int| 0 <= k < w.len() implies 1 <= #[trigger] (w[k] as int) <= stairs.len() by {};
        }
        (stairs, w, heights)
    } else {
        (stairs, widths, heights)
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

fn build_input(stairs: &[i64], widths: &[usize], heights: &[i64]) -> String {
    let n = stairs.len();
    let m = widths.len();
    let mut s = format!("{}\n", n);
    let parts: Vec<String> = stairs.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s.push_str(&format!("{}\n", m));
    for i in 0..m {
        s.push_str(&format!("{} {}\n", widths[i], heights[i]));
    }
    s
}

fn build_output(ans: &[i64]) -> String {
    let mut s = String::new();
    for &a in ans {
        s.push_str(&format!("{}\n", a));
    }
    s
}

fn random_stairs(rng: &mut Rng, n: usize, max: i64) -> Vec<i64> {
    let mut v = Vec::with_capacity(n);
    let mut cur: i64 = rng.gen_range_i64(1, 1000);
    for _ in 0..n {
        v.push(cur);
        cur += rng.gen_range_i64(0, max / (n as i64 + 1) + 1);
        if cur > max { cur = max; }
    }
    v
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(272);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // Examples
    {
        let stairs = vec![1i64, 2, 3, 6, 6];
        let widths = vec![1usize, 3, 1, 4];
        let heights = vec![1i64, 1, 1, 3];
        let (stairs, widths, heights) = generate_test_case(stairs, widths, heights);
        let inp = build_input(&stairs, &widths, &heights);
        if seen.insert(inp.clone()) {
            let ans = Solution::landing_heights(stairs, widths, heights);
            let outp = build_output(&ans);
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }
    {
        let stairs = vec![1i64, 2, 3];
        let widths = vec![1usize, 3];
        let heights = vec![1i64, 3];
        let (stairs, widths, heights) = generate_test_case(stairs, widths, heights);
        let inp = build_input(&stairs, &widths, &heights);
        if seen.insert(inp.clone()) {
            let ans = Solution::landing_heights(stairs, widths, heights);
            let outp = build_output(&ans);
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }

    let mut tries = 0;
    while count < target && tries < target * 100 {
        tries += 1;
        let n = match tries % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(2, 20),
            2 => rng.gen_range_usize(20, 100),
            3 => rng.gen_range_usize(100, 500),
            _ => rng.gen_range_usize(500, 5000),
        };
        let max_h = match tries % 3 {
            0 => 100i64,
            1 => 1000i64,
            _ => 1_000_000_000i64,
        };
        let stairs = random_stairs(&mut rng, n, max_h);
        let m = rng.gen_range_usize(1, 30.min(n.max(1)*3));
        let mut widths = Vec::with_capacity(m);
        let mut heights = Vec::with_capacity(m);
        for _ in 0..m {
            widths.push(rng.gen_range_usize(1, n));
            heights.push(rng.gen_range_i64(1, max_h));
        }
        let (stairs, widths, heights) = generate_test_case(stairs, widths, heights);
        let inp = build_input(&stairs, &widths, &heights);
        if !seen.insert(inp.clone()) { continue; }
        let ans = Solution::landing_heights(stairs, widths, heights);
        let outp = build_output(&ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
