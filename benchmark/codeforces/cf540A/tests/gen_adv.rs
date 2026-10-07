use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    current: &Vec<u8>,
    target: &Vec<u8>,
) -> (result: (usize, Vec<u8>, Vec<u8>))
    requires
        1 <= n <= 1000,
        current.len() == n,
        target.len() == n,
        forall |i: int| 0 <= i < n as int ==> 0 <= #[trigger] current[i] <= 9,
        forall |i: int| 0 <= i < n as int ==> 0 <= #[trigger] target[i] <= 9,
    ensures
        1 <= result.0 <= 1000,
        result.1.len() == result.0,
        result.2.len() == result.0,
        forall |i: int| 0 <= i < result.0 as int ==> 0 <= #[trigger] result.1[i] <= 9,
        forall |i: int| 0 <= i < result.0 as int ==> 0 <= #[trigger] result.2[i] <= 9,
{
    let mut c: Vec<u8> = Vec::new();
    let mut t: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            c.len() == i,
            t.len() == i,
            current.len() == n,
            target.len() == n,
            forall |k: int| 0 <= k < i as int ==> 0 <= #[trigger] c[k] <= 9,
            forall |k: int| 0 <= k < i as int ==> 0 <= #[trigger] t[k] <= 9,
            forall |k: int| 0 <= k < n as int ==> 0 <= #[trigger] current[k] <= 9,
            forall |k: int| 0 <= k < n as int ==> 0 <= #[trigger] target[k] <= 9,
        decreases n - i,
    {
        c.push(current[i]);
        t.push(target[i]);
        i = i + 1;
    }
    (n, c, t)
}

}

use std::io::Write;
use std::collections::HashSet;

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
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
    let target_count: usize = 200;
    let mut rng = Rng::new(54004);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |cur: String, tgt: String, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        let n = cur.len();
        if n == 0 || n > 1000 || tgt.len() != n { return; }
        if !cur.bytes().all(|b| b.is_ascii_digit()) || !tgt.bytes().all(|b| b.is_ascii_digit()) { return; }
        let key = format!("{}_{}", cur, tgt);
        if !seen.insert(key) { return; }
        let cb: Vec<u8> = cur.bytes().map(|b| b - b'0').collect();
        let tb: Vec<u8> = tgt.bytes().map(|b| b - b'0').collect();
        let result = Solution::min_lock_moves(n, cb, tb);
        let inp = format!("{}\n{}\n{}\n", n, cur, tgt);
        let outp = format!("{}\n", result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // Adversarial: max length with worst-case differences (all 5s)
    let l1000_zeros: String = (0..1000).map(|_| '0').collect();
    let l1000_fives: String = (0..1000).map(|_| '5').collect();
    emit(l1000_zeros.clone(), l1000_fives.clone(), &mut seen, &mut out, &mut count);
    emit(l1000_fives.clone(), l1000_zeros.clone(), &mut seen, &mut out, &mut count);

    let l1000_zeros2: String = (0..1000).map(|_| '0').collect();
    let l1000_nines: String = (0..1000).map(|_| '9').collect();
    emit(l1000_zeros2.clone(), l1000_nines.clone(), &mut seen, &mut out, &mut count);
    emit(l1000_nines.clone(), l1000_zeros2.clone(), &mut seen, &mut out, &mut count);

    // Pattern where d=5 vs d=4
    for d in 0..=9 {
        let cur: String = std::iter::repeat(((b'0' + 0) as char)).take(1000).collect();
        let tgt: String = std::iter::repeat(((b'0' + d) as char)).take(1000).collect();
        emit(cur, tgt, &mut seen, &mut out, &mut count);
    }

    // All 9 -> 0
    for d in 0..=9u8 {
        let cur: String = std::iter::repeat((b'0' + d) as char).take(500).collect();
        let tgt: String = std::iter::repeat((b'0' + ((d + 5) % 10)) as char).take(500).collect();
        emit(cur, tgt, &mut seen, &mut out, &mut count);
    }

    while count < target_count {
        let n = match count % 5 {
            0 | 1 => rng.gen_range_usize(500, 1000),
            2 => rng.gen_range_usize(100, 500),
            3 => rng.gen_range_usize(20, 200),
            _ => rng.gen_range_usize(1, 50),
        };
        let cur: String = (0..n).map(|_| (b'0' + rng.gen_range_i64(0, 9) as u8) as char).collect();
        let tgt: String = (0..n).map(|_| (b'0' + rng.gen_range_i64(0, 9) as u8) as char).collect();
        emit(cur, tgt, &mut seen, &mut out, &mut count);
    }
}

