use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    s_gaps: &Vec<u32>,   // gap between s[i-1] and s[i], must be >= 1 for i>=1; s[0] is s_gaps[0]
    d_vals: &Vec<u32>,   // duration added on top of max(s[i], f[i-1]); must be >= 1
) -> (result: (Vec<i64>, Vec<i64>))
    requires
        1 <= n <= 200_000,
        s_gaps.len() == n,
        d_vals.len() == n,
        // s[0] constraint: s_gaps[0] in [0, 1000]
        s_gaps[0] <= 1000,
        // subsequent gaps at least 1 and at most 1000
        forall |k: int| 1 <= k < n ==> 1 <= #[trigger] s_gaps[k] <= 1000,
        // durations at least 1 and at most 1000
        forall |k: int| 0 <= k < n ==> 1 <= #[trigger] d_vals[k] <= 1000,
    ensures
        result.0.len() == n,
        result.1.len() == n,
        result.0.len() == result.1.len(),
        forall |k: int| 0 <= k < result.0.len() ==> 0 <= #[trigger] result.0[k] <= 1_000_000_000,
        forall |k: int| 0 <= k < result.1.len() ==> 0 <= #[trigger] result.1[k] <= 1_000_000_000,
        forall |k: int| 0 <= k < result.0.len() ==> result.0[k] < result.1[k],
        forall |k: int| 0 <= k < result.0.len() - 1 ==> #[trigger] result.0[k] < result.0[k + 1],
        forall |k: int| 0 <= k < result.1.len() - 1 ==> #[trigger] result.1[k] < result.1[k + 1],
{
    let mut s: Vec<i64> = Vec::new();
    let mut f: Vec<i64> = Vec::new();

    // We'll build s[i] and f[i] step by step.
    // s[0] = s_gaps[0]
    // s[i] = s[i-1] + s_gaps[i]
    // start_i = max(s[i], f[i-1])  (for i=0, start=s[0])
    // f[i] = start_i + d_vals[i]
    // We need f[i] <= 1e9. Since n<=200_000 and each gap/d <= 1000, max is bounded.
    // s[i] <= 1000 * n <= 2e8, f[i] <= s[i] + sum of d <= 2e8 + 2e8 = 4e8 <= 1e9. Good.

    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            s.len() == i,
            f.len() == i,
            n <= 200_000,
            s_gaps.len() == n,
            d_vals.len() == n,
            s_gaps[0] <= 1000,
            forall |k: int| 1 <= k < n ==> 1 <= #[trigger] s_gaps[k] <= 1000,
            forall |k: int| 0 <= k < n ==> 1 <= #[trigger] d_vals[k] <= 1000,
            // bounds
            forall |k: int| 0 <= k < i ==> 0 <= #[trigger] s[k] <= 500_000_000,
            forall |k: int| 0 <= k < i ==> 0 <= #[trigger] f[k] <= 900_000_000,
            // ordering
            forall |k: int| 0 <= k < i ==> #[trigger] s[k] < f[k],
            forall |k: int| 0 <= k < (i as int) - 1 ==> #[trigger] s[k] < s[k + 1],
            forall |k: int| 0 <= k < (i as int) - 1 ==> #[trigger] f[k] < f[k + 1],
            // f[i-1] related bounds: if i>0, s[i-1] <= 1000*i, f[i-1] <= 2000*i
            i > 0 ==> s[i - 1] as int <= 1000 * (i as int),
            i > 0 ==> f[i - 1] as int <= 2000 * (i as int),
        decreases n - i,
    {
        let si: i64 = if i == 0 {
            s_gaps[0] as i64
        } else {
            let prev = s[i - 1];
            prev + s_gaps[i] as i64
        };

        let start: i64 = if i == 0 {
            si
        } else {
            let fp = f[i - 1];
            if si > fp { si } else { fp }
        };

        let fi: i64 = start + d_vals[i] as i64;

        proof {
            if i == 0 {
                assert(si as int == s_gaps[0] as int);
                assert(si <= 1000);
                assert(start == si);
                assert(fi as int == si as int + d_vals[0] as int);
                assert(fi <= 2000);
            } else {
                assert(s[i - 1] as int <= 1000 * (i as int));
                assert(f[i - 1] as int <= 2000 * (i as int));
                assert(s_gaps[i as int] <= 1000);
                assert(si as int == s[i - 1] as int + s_gaps[i as int] as int);
                assert(si as int <= 1000 * (i as int) + 1000);
                assert(si as int <= 1000 * ((i + 1) as int));
                assert(start as int <= 2000 * (i as int) + 1000);
                assert(fi as int <= 2000 * (i as int) + 1000 + 1000);
                assert(fi as int <= 2000 * ((i + 1) as int));
                assert(s[i - 1] < si);
                assert(f[i - 1] <= start);
                assert(f[i - 1] < fi);
            }
            assert(start >= si);
            assert(fi > start);
            assert(si < fi);
        }

        s.push(si);
        f.push(fi);

        proof {
            // reestablish invariants
            assert(s.len() == i + 1);
            assert(f.len() == i + 1);
            assert(s[i as int] == si);
            assert(f[i as int] == fi);
        }

        i = i + 1;
    }

    proof {
        assert(n <= 200_000);
        // bounds implied
        assert forall |k: int| 0 <= k < s.len() implies 0 <= #[trigger] s[k] <= 1_000_000_000 by {
            assert(s[k] <= 500_000_000);
        }
        assert forall |k: int| 0 <= k < f.len() implies 0 <= #[trigger] f[k] <= 1_000_000_000 by {
            assert(f[k] <= 900_000_000);
        }
    }

    (s, f)
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
        let x = self.next_u64();
        let v = ((x >> 32) ^ x) as u128;
        (lo as i128 + (v % r) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let x = self.next_u64();
        let v = ((x >> 32) ^ x) as usize;
        lo + v % (hi - lo + 1)
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

fn build_input(cases: &[(Vec<i64>, Vec<i64>)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (sv, fv) in cases {
        s.push_str(&format!("{}\n", sv.len()));
        let p1: Vec<String> = sv.iter().map(|v| v.to_string()).collect();
        s.push_str(&p1.join(" "));
        s.push('\n');
        let p2: Vec<String> = fv.iter().map(|v| v.to_string()).collect();
        s.push_str(&p2.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[Vec<i64>]) -> String {
    let mut s = String::new();
    for d in answers {
        let parts: Vec<String> = d.iter().map(|v| v.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_valid(rng: &mut Rng, n: usize, max_t: i64) -> (Vec<i64>, Vec<i64>) {
    let mut s_vec: Vec<i64> = Vec::with_capacity(n);
    let mut last = 0i64;
    for _ in 0..n {
        let nv = last + 1 + rng.gen_range_i64(0, max_t / (n as i64 + 1));
        s_vec.push(nv);
        last = nv;
    }
    let mut f_vec: Vec<i64> = Vec::with_capacity(n);
    let mut last_f: i64 = 0;
    for i in 0..n {
        let lo = std::cmp::max(s_vec[i] + 1, last_f + 1);
        let hi = std::cmp::min(max_t, lo + max_t / (n as i64 + 1));
        let nv = if hi > lo { rng.gen_range_i64(lo, hi) } else { lo };
        f_vec.push(nv);
        last_f = nv;
    }
    (s_vec, f_vec)
}

fn make_test(rng: &mut Rng, mode: usize) -> (Vec<i64>, Vec<i64>) {
    match mode {
        0 => (vec![0], vec![1_000_000_000]),
        1 => {
            let n = rng.gen_range_usize(1, 50);
            build_valid(rng, n, 1_000_000_000)
        }
        2 => {
            // Tasks always overlap (s[i] < f[i-1])
            let n = rng.gen_range_usize(2, 30);
            let mut s_v: Vec<i64> = (0..n as i64).collect();
            let mut f_v: Vec<i64> = (n as i64..2 * n as i64).collect();
            (s_v, f_v)
        }
        3 => {
            // Tasks never overlap
            let n = rng.gen_range_usize(1, 30);
            let mut s_v: Vec<i64> = Vec::new();
            let mut f_v: Vec<i64> = Vec::new();
            let mut t = 0i64;
            for _ in 0..n {
                s_v.push(t);
                t += rng.gen_range_i64(1, 10);
                f_v.push(t);
                t += rng.gen_range_i64(1, 10);
            }
            (s_v, f_v)
        }
        4 => {
            // Tasks complete instantly (f[i] = s[i] + 1)
            let n = rng.gen_range_usize(1, 50);
            let s_v: Vec<i64> = (0..n as i64).map(|i| i * 3).collect();
            let f_v: Vec<i64> = s_v.iter().map(|&x| x + 1).collect();
            (s_v, f_v)
        }
        5 => {
            let n = 100;
            build_valid(rng, n, 1_000_000_000)
        }
        6 => {
            // Largest values
            let n = rng.gen_range_usize(1, 5);
            build_valid(rng, n, 1_000_000_000)
        }
        7 => {
            let n = rng.gen_range_usize(1, 20);
            build_valid(rng, n, 1_000_000)
        }
        8 => {
            let n = rng.gen_range_usize(1, 20);
            build_valid(rng, n, 100)
        }
        9 => {
            let n = rng.gen_range_usize(1, 50);
            build_valid(rng, n, 100_000)
        }
        _ => {
            let n = rng.gen_range_usize(1, 30);
            build_valid(rng, n, 1000)
        }
    }
}

fn main() {
    let mut rng = Rng::new(1);
    let modes = 10usize;
    let total = 200usize;

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;
    let mut idx = 0;
    while count < total {
        let t: usize = if count < 10 { 1 } else { rng.gen_range_usize(1, 10) };
        let mut cases: Vec<(Vec<i64>, Vec<i64>)> = Vec::new();
        for _ in 0..t {
            let mode = idx % modes;
            idx += 1;
            cases.push(make_test(&mut rng, mode));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<Vec<i64>> = cases.iter().map(|(s, f)| Solution::restore_durations(s.clone(), f.clone())).collect();
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

