use vstd::prelude::*;

verus! {

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

// Lemma: count_segments with p = 1_000_000_000 returns 0 if all a[i] <= p.
proof fn lemma_count_segments_max(s: Seq<char>, a: Seq<i32>, p: i32, end: int)
    requires
        0 <= end <= a.len(),
        a.len() == s.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] <= p,
    ensures
        count_segments(s, a, p, end) == (0int, false),
    decreases end,
{
    if end <= 0 {
        // base case
    } else {
        lemma_count_segments_max(s, a, p, end - 1);
        // a[end - 1] <= p so we go through the else branch
    }
}

pub fn generate_test_case(
    seed_n: usize,
    seed_k: i32,
    seed_s: &Vec<char>,
    seed_a: &Vec<i32>,
) -> (result: (usize, i32, Vec<char>, Vec<i32>))
    requires
        1 <= seed_n <= 300000,
        0 <= seed_k <= seed_n,
        seed_s.len() == seed_n,
        seed_a.len() == seed_n,
        forall|i: int| 0 <= i && i < seed_n ==> seed_s@[i] == 'R' || seed_s@[i] == 'B',
        forall|i: int| 0 <= i && i < seed_n ==> 1 <= seed_a@[i] && seed_a@[i] <= 1000000000,
    ensures
        1 <= result.0 <= 300000,
        0 <= result.1 <= result.0,
        result.2.len() == result.0,
        result.3.len() == result.0,
        forall|i: int| 0 <= i && i < result.0 ==> result.2@[i] == 'R' || result.2@[i] == 'B',
        forall|i: int| 0 <= i && i < result.0 ==> 1 <= result.3@[i] && result.3@[i] <= 1000000000,
        valid_for_penalty(result.0, result.1, result.2@, result.3@, 1000000000),
{
    let n = seed_n;
    let k = seed_k;
    // Copy seed_s into a new Vec
    let mut s_out: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == seed_s.len(),
            n == seed_a.len(),
            1 <= n <= 300000,
            0 <= i <= n,
            s_out.len() == i,
            forall|j: int| 0 <= j < seed_s.len() ==> seed_s@[j] == 'R' || seed_s@[j] == 'B',
            forall|j: int| 0 <= j < i as int ==> #[trigger] s_out@[j] == seed_s@[j],
        decreases n - i,
    {
        s_out.push(seed_s[i]);
        i = i + 1;
    }
    // Copy seed_a into a new Vec
    let mut a_out: Vec<i32> = Vec::new();
    let mut j: usize = 0;
    while j < n
        invariant
            n == seed_a.len(),
            1 <= n <= 300000,
            0 <= j <= n,
            a_out.len() == j,
            forall|jj: int| 0 <= jj < seed_a.len() ==> 1 <= seed_a@[jj] && seed_a@[jj] <= 1000000000,
            forall|jj: int| 0 <= jj < j as int ==> #[trigger] a_out@[jj] == seed_a@[jj],
        decreases n - j,
    {
        a_out.push(seed_a[j]);
        j = j + 1;
    }
    // Prove valid_for_penalty
    proof {
        lemma_count_segments_max(s_out@, a_out@, 1000000000, n as int);
    }
    (n, k, s_out, a_out)
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

fn random_seed(rng: &mut Rng, mode: usize) -> Case {
    let n = match mode {
        0 => rng.gen_range_usize(1, 5),
        1 => rng.gen_range_usize(6, 20),
        2 => rng.gen_range_usize(21, 100),
        3 => rng.gen_range_usize(101, 500),
        4 => rng.gen_range_usize(501, 2000),
        5 => rng.gen_range_usize(2001, 5000),
        _ => rng.gen_range_usize(1, 1000),
    };
    let k_choice = mode % 4;
    let k = match k_choice {
        0 => 0,
        1 => n as i32,
        2 => rng.gen_range_i64(0, n as i64) as i32,
        _ => (n as i32 / 2).max(0),
    };
    let mut s = Vec::with_capacity(n);
    let pat = mode % 5;
    for i in 0..n {
        let c = match pat {
            0 => if rng.next_u64() % 2 == 0 { 'B' } else { 'R' },
            1 => 'B',
            2 => 'R',
            3 => if i % 2 == 0 { 'B' } else { 'R' },
            _ => if i < n / 2 { 'B' } else { 'R' },
        };
        s.push(c);
    }
    let mut a = Vec::with_capacity(n);
    for _ in 0..n {
        let val = match mode % 3 {
            0 => rng.gen_range_i64(1, 1_000_000_000),
            1 => rng.gen_range_i64(999_900_000, 1_000_000_000),
            _ => rng.gen_range_i64(1, 100),
        };
        a.push(val as i32);
    }
    Case { n, k, s, a }
}

fn solve_case(c: &Case) -> i32 {
    Solution::min_penalty(c.n, c.k, c.s.clone(), c.a.clone())
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(0x70CE);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    while count < target {
        let t: usize = if count < 50 {
            rng.gen_range_usize(1, 3)
        } else if count < 150 {
            rng.gen_range_usize(2, 15)
        } else {
            rng.gen_range_usize(15, 50)
        };
        let mut cases: Vec<Case> = Vec::with_capacity(t);
        let mut total_n = 0usize;
        for _ in 0..t {
            let mode = rng.gen_range_usize(0, 6);
            let seed = random_seed(&mut rng, mode);
            // Validate seed - must satisfy: 1 <= n <= 300000, 0 <= k <= n, s len == n, a len == n,
            // s chars in {R, B}, a in [1, 1_000_000_000]
            if seed.n < 1 || seed.n > 300000 { continue; }
            if seed.k < 0 || seed.k > seed.n as i32 { continue; }
            if seed.s.len() != seed.n || seed.a.len() != seed.n { continue; }
            let mut ok = true;
            for &c in &seed.s {
                if c != 'R' && c != 'B' { ok = false; break; }
            }
            if !ok { continue; }
            for &v in &seed.a {
                if v < 1 || v > 1_000_000_000 { ok = false; break; }
            }
            if !ok { continue; }
            if total_n + seed.n > 300_000 { break; }
            total_n += seed.n;
            let (n, k, s, a) = generate_test_case(seed.n, seed.k, &seed.s, &seed.a);
            cases.push(Case { n, k, s, a });
        }
        if cases.is_empty() { continue; }
        let answers: Vec<i32> = cases.iter().map(|c| solve_case(c)).collect();
        let inp = build_input_multi(&cases);
        let outp = build_output_multi(&answers);
        if !seen.insert(inp.clone()) { continue; }
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
