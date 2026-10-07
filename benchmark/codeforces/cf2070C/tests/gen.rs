use vstd::prelude::*;

verus! {

// Spec fn helpers copied from spec.rs
pub open spec fn count_segments(s: Seq<char>, a: Seq<i32>, p: i32, end: int) -> (int, bool)
    decreases end
{
    if end <= 0 {
        (0, false)
    } else {
        let (segs, in_b) = count_segments(s, a, p, end - 1);
        if a[end - 1] > p {
            if s[end - 1] == 'B' {
                if !in_b {
                    (segs + 1, true)
                } else {
                    (segs, true)
                }
            } else {
                (segs, false)
            }
        } else {
            (segs, in_b)
        }
    }
}

pub open spec fn valid_for_penalty(n: usize, k: i32, s: Seq<char>, a: Seq<i32>, p: i32) -> bool {
    count_segments(s, a, p, n as int).0 <= k as int
}

// Lemma: when all a[i] <= p, count_segments returns (0, _)
proof fn lemma_all_leq_zero_segments(s: Seq<char>, a: Seq<i32>, p: i32, end: int)
    requires
        end >= 0,
        a.len() >= end,
        s.len() >= end,
        forall|i: int| 0 <= i && i < end ==> a[i] <= p,
    ensures
        count_segments(s, a, p, end).0 == 0,
    decreases end
{
    if end > 0 {
        lemma_all_leq_zero_segments(s, a, p, end - 1);
    }
}

pub fn generate_test_case(
    s_bits: Vec<bool>,
    a_vals: Vec<i32>,
    k: i32,
    mutation_kind: u8,
) -> (result: (usize, i32, Vec<char>, Vec<i32>))
    requires
        1 <= s_bits.len() <= 300000,
        s_bits.len() == a_vals.len(),
        0 <= k && (k as int) <= (s_bits.len() as int),
        forall|i: int| 0 <= i && i < a_vals.len() ==> 1 <= #[trigger] a_vals[i] && a_vals[i] <= 1000000000,
    ensures
        1 <= result.0 && result.0 <= 300000,
        0 <= result.1 && result.1 <= result.0,
        result.2.len() == result.0,
        result.3.len() == result.0,
        forall|i: int| 0 <= i && i < result.0 ==> result.2@[i] == 'R' || result.2@[i] == 'B',
        forall|i: int| 0 <= i && i < result.0 ==> 1 <= result.3@[i] && result.3@[i] <= 1000000000,
        valid_for_penalty(result.0, result.1, result.2@, result.3@, 1000000000),
{
    let n = s_bits.len();

    // Build s from s_bits
    let mut s: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == s_bits.len(),
            s.len() == i,
            forall|j: int| 0 <= j && j < i ==> (s@[j] == 'R' || s@[j] == 'B'),
        decreases n - i,
    {
        if s_bits[i] {
            s.push('B');
        } else {
            s.push('R');
        }
        i += 1;
    }

    // Apply mutations to s
    let s = if mutation_kind == 1 {
        // Flip all: R->B, B->R
        let mut flipped: Vec<char> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == s_bits.len(),
                s.len() == n,
                flipped.len() == j,
                forall|m: int| 0 <= m && m < j ==> (flipped@[m] == 'R' || flipped@[m] == 'B'),
            decreases n - j,
        {
            if s[j] == 'B' {
                flipped.push('R');
            } else {
                flipped.push('B');
            }
            j += 1;
        }
        flipped
    } else if mutation_kind == 2 {
        // Set all to R
        let mut all_r: Vec<char> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == s_bits.len(),
                all_r.len() == j,
                forall|m: int| 0 <= m && m < j ==> all_r@[m] == 'R',
            decreases n - j,
        {
            all_r.push('R');
            j += 1;
        }
        all_r
    } else if mutation_kind == 3 {
        // Set all to B
        let mut all_b: Vec<char> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == s_bits.len(),
                all_b.len() == j,
                forall|m: int| 0 <= m && m < j ==> all_b@[m] == 'B',
            decreases n - j,
        {
            all_b.push('B');
            j += 1;
        }
        all_b
    } else {
        s
    };

    // Apply mutations to a
    let a = if mutation_kind == 4 {
        // Set all penalties to 1 (min boundary)
        let mut ones: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == s_bits.len(),
                ones.len() == j,
                forall|m: int| 0 <= m && m < j ==> ones@[m] == 1,
            decreases n - j,
        {
            ones.push(1i32);
            j += 1;
        }
        ones
    } else if mutation_kind == 5 {
        // Set all penalties to max boundary
        let mut maxes: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == s_bits.len(),
                maxes.len() == j,
                forall|m: int| 0 <= m && m < j ==> maxes@[m] == 1000000000,
            decreases n - j,
        {
            maxes.push(1000000000i32);
            j += 1;
        }
        maxes
    } else if mutation_kind == 6 && n > 1 {
        // Set first penalty to 1
        let mut a = a_vals;
        a.set(0, 1i32);
        a
    } else if mutation_kind == 7 && n > 1 {
        // Set last penalty to max
        let mut a = a_vals;
        let last = n - 1;
        a.set(last, 1000000000i32);
        a
    } else {
        a_vals
    };

    // Prove valid_for_penalty
    proof {
        lemma_all_leq_zero_segments(s@, a@, 1000000000i32, n as int);
    }

    (n, k, s, a)
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
    n: usize,
    k: i32,
    s: Vec<char>,
    a: Vec<i32>,
}

fn build_input_multi(cases: &[Case]) -> String {
    let mut s = format!("{}\n", cases.len());
    for c in cases {
        s.push_str(&format!("{} {}\n", c.n, c.k));
        let cs: String = c.s.iter().collect();
        s.push_str(&cs);
        s.push('\n');
        let parts: Vec<String> = c.a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output_multi(answers: &[i32]) -> String {
    let mut s = String::new();
    for &a in answers {
        s.push_str(&format!("{}\n", a));
    }
    s
}

fn random_case(rng: &mut Rng, mode: usize) -> Case {
    let n = match mode {
        0 => rng.gen_range_usize(1, 5),
        1 => rng.gen_range_usize(6, 20),
        2 => rng.gen_range_usize(21, 100),
        3 => rng.gen_range_usize(101, 500),
        4 => rng.gen_range_usize(501, 1000),
        _ => rng.gen_range_usize(1, 100),
    };
    let k = rng.gen_range_i64(0, n as i64) as i32;
    let mut s = Vec::with_capacity(n);
    for _ in 0..n {
        if rng.next_u64() % 2 == 0 { s.push('B'); } else { s.push('R'); }
    }
    let mut a = Vec::with_capacity(n);
    for _ in 0..n {
        a.push(rng.gen_range_i64(1, 1_000_000_000) as i32);
    }
    Case { n, k, s, a }
}

fn solve_case(c: &Case) -> i32 {
    Solution::min_penalty(c.n, c.k, c.s.clone(), c.a.clone())
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(2070);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let examples: Vec<Case> = vec![
        Case { n: 4, k: 1, s: "BRBR".chars().collect(), a: vec![9, 3, 5, 4] },
        Case { n: 4, k: 1, s: "BRBR".chars().collect(), a: vec![9, 5, 3, 4] },
        Case { n: 4, k: 2, s: "BRBR".chars().collect(), a: vec![9, 3, 5, 4] },
        Case { n: 10, k: 2, s: "BRBRBBRRBR".chars().collect(), a: vec![5, 1, 2, 4, 5, 3, 6, 1, 5, 4] },
        Case { n: 5, k: 5, s: "RRRRR".chars().collect(), a: vec![5, 3, 1, 2, 4] },
    ];
    {
        let answers: Vec<i32> = examples.iter().map(|c| solve_case(c)).collect();
        let inp = build_input_multi(&examples);
        let outp = build_output_multi(&answers);
        if seen.insert(inp.clone()) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }

    // singletons of examples
    for ex in &examples {
        if count >= target { break; }
        let cases = vec![ex.clone()];
        let answers: Vec<i32> = cases.iter().map(|c| solve_case(c)).collect();
        let inp = build_input_multi(&cases);
        let outp = build_output_multi(&answers);
        if seen.insert(inp.clone()) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }

    // tiny edge cases
    let edges: Vec<Case> = vec![
        Case { n: 1, k: 0, s: vec!['B'], a: vec![1] },
        Case { n: 1, k: 1, s: vec!['B'], a: vec![1_000_000_000] },
        Case { n: 1, k: 0, s: vec!['R'], a: vec![1_000_000_000] },
        Case { n: 2, k: 0, s: vec!['R', 'R'], a: vec![1, 1] },
        Case { n: 2, k: 1, s: vec!['B', 'B'], a: vec![1, 1] },
        Case { n: 5, k: 0, s: "BBBBB".chars().collect(), a: vec![1, 2, 3, 4, 5] },
        Case { n: 5, k: 5, s: "BRBRB".chars().collect(), a: vec![1_000_000_000; 5] },
    ];
    for chunk in edges.chunks(3) {
        if count >= target { break; }
        let cases: Vec<Case> = chunk.to_vec();
        let answers: Vec<i32> = cases.iter().map(|c| solve_case(c)).collect();
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
        let answers: Vec<i32> = cases.iter().map(|c| solve_case(c)).collect();
        let inp = build_input_multi(&cases);
        let outp = build_output_multi(&answers);
        if !seen.insert(inp.clone()) { continue; }
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

