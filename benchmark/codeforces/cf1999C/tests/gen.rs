use vstd::prelude::*;

verus! {

// Generate test cases by constructing valid intervals
pub fn generate_test_case(seed_n: usize, gap: i64, length: i64, s: i64, m_extra: i64) -> (result: (i64, i64, Vec<i64>, Vec<i64>))
    requires
        1 <= seed_n <= 50,
        1 <= gap <= 100,
        1 <= length <= 100,
        1 <= s <= 100,
        0 <= m_extra <= 100,
    ensures
        1 <= result.0 <= 1_000_000_000,
        1 <= result.1 <= 1_000_000_000,
        1 <= result.2.len() <= 200_000,
        result.2.len() == result.3.len(),
        forall|i: int| 0 <= i < result.2.len() ==> 0 <= #[trigger] result.2[i] && result.2[i] < result.3[i] && result.3[i] <= result.1,
        forall|i: int| 0 < i < result.2.len() ==> #[trigger] result.2[i] > result.3[i - 1],
{
    let mut l: Vec<i64> = Vec::new();
    let mut r: Vec<i64> = Vec::new();
    let mut pos: i64 = gap;
    let mut i: usize = 0;
    while i < seed_n
        invariant
            0 <= i <= seed_n,
            l.len() == i,
            r.len() == i,
            1 <= seed_n <= 50,
            1 <= gap <= 100,
            1 <= length <= 100,
            0 <= m_extra <= 100,
            1 <= pos,
            pos <= gap + (i as i64) * 200i64,
            forall|k: int| 0 <= k < l.len() ==> 0 <= #[trigger] l[k] && l[k] < r[k] && r[k] <= pos - gap,
            forall|k: int| 0 < k < l.len() ==> #[trigger] l[k] > r[k - 1],
            i > 0 ==> r[i as int - 1] == pos - gap,
            i > 0 ==> l[i as int - 1] == pos - gap - length,
        decreases seed_n - i,
    {
        proof {
            assert((i as i64 + 1) * 200i64 == (i as i64) * 200i64 + 200i64) by(nonlinear_arith);
        }
        l.push(pos);
        r.push(pos + length);
        pos = pos + length + gap;
        i = i + 1;
    }
    proof {
        assert(pos <= gap + (seed_n as i64) * 200i64);
        assert((seed_n as i64) * 200i64 <= 50i64 * 200i64) by(nonlinear_arith) requires seed_n <= 50;
    }
    let m = pos + m_extra;
    (s, m, l, r)
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
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
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

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1999);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f_out = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f_out);
    let mut count = 0usize;
    let mut seen = HashSet::new();

    while count < target {
        let t = if count < 5 { 1usize } else { rng.gen_range_usize(1, 5) };
        let mut input = format!("{}\n", t);
        let mut output = String::new();
        for _ in 0..t {
            let n = rng.gen_range_usize(1, 10);
            let gap = rng.gen_range_i64(1, 10);
            let length = rng.gen_range_i64(1, 10);
            let s_val = rng.gen_range_i64(1, 20);
            let m_extra = rng.gen_range_i64(0, 20);
            let (s, m, l, r) = generate_test_case(n, gap, length, s_val, m_extra);
            input.push_str(&format!("{} {} {}\n", l.len(), s, m));
            for j in 0..l.len() {
                input.push_str(&format!("{} {}\n", l[j], r[j]));
            }
            let ans = Solution::can_shower(s, m, l, r);
            output.push_str(if ans { "YES\n" } else { "NO\n" });
        }
        if !seen.insert(input.clone()) { continue; }
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&input), fmt_json_str(&output)).unwrap();
        count += 1;
    }
}
