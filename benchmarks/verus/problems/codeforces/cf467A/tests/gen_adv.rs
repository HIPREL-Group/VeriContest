use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    p_vals: &Vec<i64>,
    q_vals: &Vec<i64>,
) -> (result: (Vec<i64>, Vec<i64>))
    requires
        1 <= n <= 100,
        p_vals.len() == n,
        q_vals.len() == n,
        forall|i: int| 0 <= i < n ==> 0 <= (#[trigger] p_vals[i]) && p_vals[i] <= q_vals[i] && q_vals[i] <= 100,
    ensures
        ({
            let (p, q) = result;
            &&& p.len() == n
            &&& q.len() == n
            &&& 1 <= p.len() <= 100
            &&& p.len() == q.len()
            &&& forall|j: int| 0 <= j < p.len() ==> 0 <= (#[trigger] p[j] as int) && (p[j] as int) <= (q[j] as int) && (q[j] as int) <= 100
        }),
{
    let mut p: Vec<i64> = Vec::new();
    let mut q: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            p.len() == i,
            q.len() == i,
            p_vals.len() == n,
            q_vals.len() == n,
            forall|k: int| 0 <= k < i ==> p[k] == p_vals[k],
            forall|k: int| 0 <= k < i ==> q[k] == q_vals[k],
            forall|k: int| 0 <= k < n ==> 0 <= (#[trigger] p_vals[k]) && p_vals[k] <= q_vals[k] && q_vals[k] <= 100,
        decreases n - i,
    {
        p.push(p_vals[i]);
        q.push(q_vals[i]);
        i = i + 1;
    }
    (p, q)
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

fn build_input(p: &[i64], q: &[i64]) -> String {
    let n = p.len();
    let mut s = format!("{}\n", n);
    for i in 0..n {
        s.push_str(&format!("{} {}\n", p[i], q[i]));
    }
    s
}

fn random_pq(rng: &mut Rng) -> (i64, i64) {
    let q = rng.gen_range_i64(0, 100);
    let p = rng.gen_range_i64(0, q);
    (p, q)
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |p: Vec<i64>, q: Vec<i64>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let n = p.len();
        if !(1 <= n && n <= 100 && q.len() == n) { return; }
        for i in 0..n {
            if !(0 <= p[i] && p[i] <= q[i] && q[i] <= 100) { return; }
        }
        let key = format!("{:?}|{:?}", p, q);
        if !seen.insert(key) { return; }
        let inp = build_input(&p, &q);
        let ans = Solution::count_accommodation_rooms(p.clone(), q.clone());
        let outs = format!("{}\n", ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    let mut tries = 0usize;
    while count < target {
        tries += 1;
        if tries > 100000 { break; }
        let mode = tries % 8;
        let n = match mode {
            0 => 1,
            1 => 100,
            2 => 50,
            3 => rng.gen_range_usize(2, 10),
            4 => rng.gen_range_usize(10, 50),
            _ => rng.gen_range_usize(1, 100),
        };
        let mut p = Vec::with_capacity(n);
        let mut q = Vec::with_capacity(n);
        match mode {
            0 => { p.push(0); q.push(100); }
            1 => { for _ in 0..n { p.push(0); q.push(100); } }
            2 => { for _ in 0..n { p.push(100); q.push(100); } }
            3 => { for _ in 0..n { p.push(0); q.push(2); } }
            4 => { for _ in 0..n { p.push(0); q.push(1); } }
            _ => for _ in 0..n {
                let (pi, qi) = random_pq(&mut rng);
                p.push(pi);
                q.push(qi);
            }
        }
        emit(p, q, &mut seen, &mut out, &mut count);
    }
}

