use vstd::prelude::*;

verus! {

pub fn generate_test_case(a: Vec<i64>, mutation_kind: u8) -> (result: (usize, Vec<i64>))
    requires
        1 <= a.len() <= 400000,
        forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 1000000000000i64,
    ensures
        1 <= result.0 <= 400000,
        result.1.len() == result.0,
        forall|i: int| 0 <= i < result.0 ==> 1 <= #[trigger] result.1[i] <= 1000000000000i64,
{
    let n = a.len();
    if mutation_kind == 0 {
        // identity
        (n, a)
    } else if mutation_kind == 1 {
        // set first element to 1 (GCD becomes 1)
        let mut d = a;
        d.set(0, 1);
        (n, d)
    } else if mutation_kind == 2 {
        // set all elements to the first element (GCD = that element)
        let val = a[0];
        let mut d = a;
        let mut i: usize = 1;
        while i < d.len()
            invariant
                1 <= i <= d.len(),
                d.len() == n,
                1 <= n <= 400000,
                1 <= val <= 1000000000000i64,
                forall|j: int| 0 <= j < i ==> d[j] == val,
                forall|j: int| 0 <= j < d.len() ==> 1 <= #[trigger] d[j] <= 1000000000000i64,
            decreases d.len() - i,
        {
            d.set(i, val);
            i += 1;
        }
        (n, d)
    } else if mutation_kind == 3 && a.len() > 1 {
        // shrink by removing last element
        let mut d = a;
        d.pop();
        let new_n = d.len();
        (new_n, d)
    } else if mutation_kind == 4 && a.len() < 400000 {
        // grow by pushing element equal to first
        let val = a[0];
        let mut d = a;
        d.push(val);
        let new_n = d.len();
        (new_n, d)
    } else if mutation_kind == 5 {
        // set last element to 1
        let mut d = a;
        let last = d.len() - 1;
        d.set(last, 1);
        (n, d)
    } else if mutation_kind == 6 {
        // nudge first element: if < max, increment by 1
        let mut d = a;
        if d[0] < 1000000000000i64 {
            d.set(0, d[0] + 1);
        }
        (n, d)
    } else if mutation_kind == 7 {
        // set first element to max boundary
        let mut d = a;
        d.set(0, 1000000000000i64);
        (n, d)
    } else {
        // fallback: identity
        (n, a)
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

fn build_input(a: &[i64]) -> String {
    let mut s = format!("{}\n", a.len());
    let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(ans: i64) -> String { format!("{}\n", ans) }

fn random_array(rng: &mut Rng, len: usize, max_val: i64) -> Vec<i64> {
    (0..len).map(|_| rng.gen_range_i64(1, max_val)).collect()
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let mut seen: HashSet<u64> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |a: Vec<i64>, seen: &mut HashSet<u64>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if a.is_empty() { return; }
        let mut h: u64 = 1469598103934665603;
        h ^= a.len() as u64; h = h.wrapping_mul(1099511628211);
        for &x in &a { h ^= x as u64; h = h.wrapping_mul(1099511628211); }
        if !seen.insert(h) { return; }
        let inp = build_input(&a);
        let ans = Solution::count_common_divisors(a.len(), a.clone());
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Examples
    emit(vec![1,2,3,4,5], &mut seen, &mut out, &mut count);
    emit(vec![6,90,12,18,30,18], &mut seen, &mut out, &mut count);
    emit(vec![2,4,6,2,10], &mut seen, &mut out, &mut count);

    // Edge cases
    emit(vec![1], &mut seen, &mut out, &mut count);
    emit(vec![1_000_000_000_000], &mut seen, &mut out, &mut count);
    emit(vec![6,12,18], &mut seen, &mut out, &mut count);
    emit(vec![6,6,6], &mut seen, &mut out, &mut count);
    emit(vec![1_000_000_000_000, 1_000_000_000_000], &mut seen, &mut out, &mut count);

    let mut tries = 0;
    while count < target && tries < 5000 {
        tries += 1;
        let n = match tries % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(5, 50),
            3 => rng.gen_range_usize(20, 200),
            _ => rng.gen_range_usize(100, 1000),
        };
        let max_val = match tries % 4 {
            0 => 10i64,
            1 => 100,
            2 => 1_000_000,
            _ => 1_000_000_000_000,
        };
        let v = random_array(&mut rng, n, max_val);
        emit(v, &mut seen, &mut out, &mut count);
    }
}

