use vstd::prelude::*;

verus! {

pub open spec fn rightmost_one(s: Seq<u8>, len: int) -> int
    decreases len,
{
    if len <= 0 {
        0int
    } else if s[len - 1] == 1u8 {
        len - 1
    } else {
        rightmost_one(s, len - 1)
    }
}

pub open spec fn leftmost_zero(s: Seq<u8>, start: int) -> int
    decreases s.len() - start,
{
    if start >= s.len() {
        s.len() - 1
    } else if s[start] == 0u8 {
        start
    } else {
        leftmost_zero(s, start + 1)
    }
}

// Build a string: 1's in [0, ones), ?'s in [ones, ones+qs), 0's in [ones+qs, n).
// This always satisfies rightmost_one <= leftmost_zero.
pub fn generate_test_case(
    n: usize,
    ones: usize,
    qs: usize,
) -> (result: Vec<u8>)
    requires
        1 <= n <= 200000,
        ones + qs <= n,
    ensures
        1 <= result.len() <= 200000,
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] <= 2u8,
        rightmost_one(result@, result.len() as int) <= leftmost_zero(result@, 0),
{
    let mut v: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < ones
        invariant
            0 <= i <= ones,
            ones + qs <= n,
            v.len() == i,
            forall|k: int| 0 <= k < i ==> v[k] == 1u8,
        decreases ones - i,
    {
        v.push(1u8);
        i += 1;
    }
    let mut j: usize = 0;
    while j < qs
        invariant
            0 <= j <= qs,
            ones + qs <= n,
            v.len() == ones + j,
            forall|k: int| 0 <= k < ones ==> v[k] == 1u8,
            forall|k: int| ones <= k < ones + j ==> v[k] == 2u8,
        decreases qs - j,
    {
        v.push(2u8);
        j += 1;
    }
    let zeros = n - ones - qs;
    let mut k: usize = 0;
    while k < zeros
        invariant
            0 <= k <= zeros,
            ones + qs + zeros == n,
            v.len() == ones + qs + k,
            forall|t: int| 0 <= t < ones ==> v[t] == 1u8,
            forall|t: int| ones <= t < ones + qs ==> v[t] == 2u8,
            forall|t: int| ones + qs <= t < ones + qs + k ==> v[t] == 0u8,
        decreases zeros - k,
    {
        v.push(0u8);
        k += 1;
    }
    proof {
        // Establish that all elements are <= 2
        assert(forall|i: int| 0 <= i < v.len() ==> v[i] <= 2u8);
        // Show rightmost_one <= leftmost_zero by constructive argument
        // rightmost_one of v: scanning from right, we have zeros first, then qs, then ones.
        // If zeros > 0, rightmost_one walks past all zeros and qs to land at ones-1.
        lemma_rightmost_one_for_construction(v@, n as int, ones as int, qs as int);
        lemma_leftmost_zero_for_construction(v@, n as int, ones as int, qs as int);
    }
    v
}

proof fn lemma_rightmost_one_for_construction(s: Seq<u8>, n: int, ones: int, qs: int)
    requires
        0 <= n,
        0 <= ones,
        0 <= qs,
        ones + qs <= s.len(),
        s.len() >= n,
        forall|i: int| 0 <= i < ones ==> s[i] == 1u8,
        forall|i: int| ones <= i < ones + qs ==> s[i] == 2u8,
        forall|i: int| ones + qs <= i < s.len() ==> s[i] == 0u8,
    ensures
        rightmost_one(s, n) <= ones,
    decreases n,
{
    if n <= 0 {
    } else if s[n - 1] == 1u8 {
    } else {
        lemma_rightmost_one_for_construction(s, n - 1, ones, qs);
    }
}

proof fn lemma_leftmost_zero_for_construction(s: Seq<u8>, n: int, ones: int, qs: int)
    requires
        1 <= n,
        0 <= ones,
        0 <= qs,
        ones + qs <= n,
        s.len() == n,
        forall|i: int| 0 <= i < ones ==> s[i] == 1u8,
        forall|i: int| ones <= i < ones + qs ==> s[i] == 2u8,
        forall|i: int| ones + qs <= i < n ==> s[i] == 0u8,
    ensures
        leftmost_zero(s, 0) >= ones + qs || leftmost_zero(s, 0) == n - 1,
{
    lemma_leftmost_zero_helper(s, 0, n, ones, qs);
}

proof fn lemma_leftmost_zero_helper(s: Seq<u8>, start: int, n: int, ones: int, qs: int)
    requires
        1 <= n,
        0 <= ones,
        0 <= qs,
        ones + qs <= n,
        s.len() == n,
        0 <= start <= ones + qs,
        forall|i: int| 0 <= i < ones ==> s[i] == 1u8,
        forall|i: int| ones <= i < ones + qs ==> s[i] == 2u8,
        forall|i: int| ones + qs <= i < n ==> s[i] == 0u8,
    ensures
        leftmost_zero(s, start) >= ones + qs || leftmost_zero(s, start) == n - 1,
    decreases ones + qs - start,
{
    if start >= n {
    } else if s[start] == 0u8 {
    } else {
        if start + 1 <= ones + qs {
            lemma_leftmost_zero_helper(s, start + 1, n, ones, qs);
        } else {
            assert(start == ones + qs);
            assert(start >= n);
        }
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

fn vec_to_string(v: &Vec<u8>) -> String {
    v.iter().map(|&b| match b { 0 => '0', 1 => '1', _ => '?' }).collect()
}

fn build_input(s: &str) -> String {
    format!("1\n{}\n", s)
}

fn solve_str(s: &str) -> usize {
    let v: Vec<u8> = s.bytes().map(|b| match b {
        b'0' => 0u8, b'1' => 1u8, _ => 2u8,
    }).collect();
    Solution::count_suspects(v)
}

fn build_output(ans: usize) -> String { format!("{}\n", ans) }

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1675);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let examples = vec![
        "0", "1", "1110000", "?????", "1?1??", "0?00?", "?????", "11??0??",
    ];
    for ex in &examples {
        if count >= target { break; }
        let inp = build_input(ex);
        if !seen.insert(inp.clone()) { continue; }
        let ans = solve_str(ex);
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    let mut tries = 0;
    while count < target && tries < target * 50 {
        tries += 1;
        let n = match tries % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(10, 50),
            3 => rng.gen_range_usize(50, 100),
            _ => rng.gen_range_usize(100, 1000),
        };
        let ones = rng.gen_range_usize(0, n);
        let qs = if n > ones { rng.gen_range_usize(0, n - ones) } else { 0 };
        let v = generate_test_case(n, ones, qs);
        let s = vec_to_string(&v);
        let inp = build_input(&s);
        if !seen.insert(inp.clone()) { continue; }
        let ans = solve_str(&s);
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
