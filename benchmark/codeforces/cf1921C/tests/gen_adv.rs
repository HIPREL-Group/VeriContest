use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    f_val: i64,
    a_val: i64,
    b_val: i64,
    step: i64,
) -> (result: (Vec<i64>, i64, i64, i64))
    requires
        1 <= n <= 200_000,
        1 <= f_val <= 1_000_000_000,
        1 <= a_val <= 1_000_000_000,
        1 <= b_val <= 1_000_000_000,
        1 <= step,
        (n as int) * (step as int) <= 1_000_000_000int,
    ensures
        ({
            let (m, f, a, b) = result;
            &&& m.len() == n
            &&& 1 <= m.len() <= 200_000
            &&& f == f_val
            &&& a == a_val
            &&& b == b_val
            &&& 1 <= f <= 1_000_000_000
            &&& 1 <= a <= 1_000_000_000
            &&& 1 <= b <= 1_000_000_000
            &&& (forall |j: int| 0 <= j < m.len() ==> 1 <= #[trigger] m[j] <= 1_000_000_000)
            &&& (forall |j: int| 1 <= j < m.len() ==> #[trigger] m[j - 1] < m[j])
        }),
{
    let mut m: Vec<i64> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            0 <= i <= n,
            1 <= n <= 200_000,
            1 <= step,
            (n as int) * (step as int) <= 1_000_000_000int,
            m.len() == i,
            forall |j: int| 0 <= j < i as int ==> 1 <= #[trigger] m[j] <= 1_000_000_000,
            forall |j: int| 1 <= j < i as int ==> #[trigger] m[j - 1] < m[j],
            forall |j: int| 0 <= j < i as int ==> #[trigger] m[j] == (j + 1) * (step as int),
        decreases n - i,
    {
        let idx: i64 = (i as i64) + 1;
        assert(idx as int == i as int + 1);
        assert(1 <= idx as int <= n as int);
        assert((idx as int) * (step as int) <= i64::MAX as int) by (nonlinear_arith)
            requires
                idx as int <= n as int,
                0 <= step as int,
                (n as int) * (step as int) <= 1_000_000_000int,
                1_000_000_000int <= i64::MAX as int,
        {
        }
        let val: i64 = idx * step;
        assert(val as int == (idx as int) * (step as int));
        assert(1 <= val as int) by (nonlinear_arith)
            requires
                1 <= idx as int,
                1 <= step as int,
                val as int == (idx as int) * (step as int),
        {
        }
        assert(val as int <= 1_000_000_000int) by (nonlinear_arith)
            requires
                idx as int <= n as int,
                0 <= step as int,
                (n as int) * (step as int) <= 1_000_000_000int,
                val as int == (idx as int) * (step as int),
        {
        }

        if i >= 1 {
            assert(m[(i - 1) as int] == (i as int) * (step as int));
            assert((i as int) * (step as int) < (idx as int) * (step as int)) by (nonlinear_arith)
                requires
                    idx as int == i as int + 1,
                    1 <= step as int,
            {
            }
            assert(m[(i - 1) as int] < val);
        }

        m.push(val);
        assert(m[i as int] == val);
        i = i + 1;
    }

    (m, f_val, a_val, b_val)
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

type Case = (i64, i64, i64, Vec<i64>);

fn build_input(cases: &[Case]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (f, a, b, m) in cases {
        s.push_str(&format!("{} {} {} {}\n", m.len(), f, a, b));
        let p: Vec<String> = m.iter().map(|x| x.to_string()).collect();
        s.push_str(&p.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[bool]) -> String {
    let mut s = String::new();
    for &a in answers { s.push_str(if a {"YES\n"} else {"NO\n"}); }
    s
}

fn solve(c: &Case) -> bool {
    Solution::can_send_all_messages(c.3.clone(), c.0, c.1, c.2)
}

fn random_case(rng: &mut Rng, n: usize, gap_max: i64) -> Case {
    let f = rng.gen_range_i64(1, 1_000_000_000);
    let a = rng.gen_range_i64(1, 1_000_000_000);
    let b = rng.gen_range_i64(1, 1_000_000_000);
    let mut m: Vec<i64> = Vec::with_capacity(n);
    let mut last = 0i64;
    for _ in 0..n {
        let nx = (last + rng.gen_range_i64(1, gap_max)).min(1_000_000_000);
        if nx <= last { break; }
        m.push(nx);
        last = nx;
        if last >= 1_000_000_000 { break; }
    }
    if m.is_empty() { m.push(1); }
    (f, a, b, m)
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(31415);
    let mut seen: HashSet<String> = HashSet::new();

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // Big single
    let big_singles: Vec<Case> = vec![
        (1_000_000_000, 1, 1, (1..=100_000).collect()),
        (1, 1, 1, vec![1_000_000_000]),
        (1_000_000_000, 1_000_000_000, 1_000_000_000, (1..=10).collect()),
    ];
    for ec in &big_singles {
        if count >= target { break; }
        let cases = vec![ec.clone()];
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<bool> = cases.iter().map(|c| solve(c)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }

    while count < target {
        let mode = rng.next_u64() % 4;
        let mut cases: Vec<Case> = Vec::new();
        let mut total_n = 0usize;
        match mode {
            0 => {
                let t = rng.gen_range_usize(20, 100);
                for _ in 0..t {
                    let n = rng.gen_range_usize(1, 30);
                    if total_n + n > 200_000 { break; }
                    let c = random_case(&mut rng, n, 1000);
                    total_n += c.3.len();
                    cases.push(c);
                }
            }
            1 => {
                let t = rng.gen_range_usize(2, 5);
                for _ in 0..t {
                    let n = rng.gen_range_usize(5000, 30_000);
                    if total_n + n > 200_000 { break; }
                    let c = random_case(&mut rng, n, 100_000);
                    total_n += c.3.len();
                    cases.push(c);
                }
            }
            2 => {
                let n = rng.gen_range_usize(50_000, 100_000);
                let c = random_case(&mut rng, n, 1000);
                cases.push(c);
            }
            _ => {
                let t = rng.gen_range_usize(5, 30);
                for _ in 0..t {
                    let n = rng.gen_range_usize(1, 1000);
                    if total_n + n > 200_000 { break; }
                    let c = random_case(&mut rng, n, 1_000_000);
                    total_n += c.3.len();
                    cases.push(c);
                }
            }
        }
        if cases.is_empty() { continue; }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<bool> = cases.iter().map(|c| solve(c)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

