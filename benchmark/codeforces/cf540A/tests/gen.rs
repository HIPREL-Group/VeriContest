use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    current: Vec<u8>,
    target: Vec<u8>,
    mutation_kind: u8,
) -> (result: (usize, Vec<u8>, Vec<u8>))
    requires
        1 <= current.len() <= 1000,
        current.len() == target.len(),
        forall|i: int| 0 <= i < current.len() ==> 0 <= #[trigger] current[i] <= 9,
        forall|i: int| 0 <= i < target.len() ==> 0 <= #[trigger] target[i] <= 9,
    ensures
        1 <= result.0 <= 1000,
        result.1.len() == result.0,
        result.2.len() == result.0,
        forall|i: int|
            0 <= i < result.0 as int ==> 0 <= #[trigger] result.1[i] <= 9,
        forall|i: int|
            0 <= i < result.0 as int ==> 0 <= #[trigger] result.2[i] <= 9,
{
    let n = current.len();
    if mutation_kind == 0 {
        // identity
        (n, current, target)
    } else if mutation_kind == 1 {
        // set all current digits to 0
        let mut cur = current;
        let mut i: usize = 0;
        while i < n
            invariant
                n == cur.len(),
                n == target.len(),
                1 <= n <= 1000,
                forall|j: int| 0 <= j < i ==> cur[j] == 0u8,
                forall|j: int| i <= j < n ==> cur[j] == current[j],
                forall|j: int| 0 <= j < n ==> 0 <= #[trigger] current[j] <= 9,
                forall|j: int| 0 <= j < n ==> 0 <= #[trigger] target[j] <= 9,
            decreases n - i,
        {
            cur.set(i, 0u8);
            i += 1;
        }
        (n, cur, target)
    } else if mutation_kind == 2 {
        // set all target digits to 9
        let mut tgt = target;
        let mut i: usize = 0;
        while i < n
            invariant
                n == current.len(),
                n == tgt.len(),
                1 <= n <= 1000,
                forall|j: int| 0 <= j < i ==> tgt[j] == 9u8,
                forall|j: int| i <= j < n ==> tgt[j] == target[j],
                forall|j: int| 0 <= j < n ==> 0 <= #[trigger] current[j] <= 9,
                forall|j: int| 0 <= j < n ==> 0 <= #[trigger] target[j] <= 9,
            decreases n - i,
        {
            tgt.set(i, 9u8);
            i += 1;
        }
        (n, current, tgt)
    } else if mutation_kind == 3 {
        // set current = target (zero moves)
        let mut cur = current;
        let mut i: usize = 0;
        while i < n
            invariant
                n == cur.len(),
                n == target.len(),
                1 <= n <= 1000,
                forall|j: int| 0 <= j < i ==> cur[j] == target[j],
                forall|j: int| i <= j < n ==> cur[j] == current[j],
                forall|j: int| 0 <= j < n ==> 0 <= #[trigger] current[j] <= 9,
                forall|j: int| 0 <= j < n ==> 0 <= #[trigger] target[j] <= 9,
            decreases n - i,
        {
            cur.set(i, target[i]);
            i += 1;
        }
        (n, cur, target)
    } else if mutation_kind == 4 {
        // swap current and target
        (n, target, current)
    } else if mutation_kind == 5 {
        // nudge first current digit up (mod 10)
        let mut cur = current;
        let old = cur[0];
        let new_val: u8 = if old < 9 { (old + 1) as u8 } else { 0u8 };
        cur.set(0, new_val);
        (n, cur, target)
    } else if mutation_kind == 6 {
        // nudge first target digit down (mod 10)
        let mut tgt = target;
        let old = tgt[0];
        let new_val: u8 = if old > 0 { (old - 1) as u8 } else { 9u8 };
        tgt.set(0, new_val);
        (n, current, tgt)
    } else if mutation_kind == 7 {
        // set all digits to 5 (max circular distance from 0)
        let mut cur = current;
        let mut tgt = target;
        let mut i: usize = 0;
        while i < n
            invariant
                n == cur.len(),
                n == tgt.len(),
                1 <= n <= 1000,
                forall|j: int| 0 <= j < i ==> cur[j] == 5u8,
                forall|j: int| 0 <= j < i ==> tgt[j] == 5u8,
                forall|j: int| i <= j < n ==> cur[j] == current[j],
                forall|j: int| i <= j < n ==> tgt[j] == target[j],
                forall|j: int| 0 <= j < n ==> 0 <= #[trigger] current[j] <= 9,
                forall|j: int| 0 <= j < n ==> 0 <= #[trigger] target[j] <= 9,
            decreases n - i,
        {
            cur.set(i, 5u8);
            tgt.set(i, 5u8);
            i += 1;
        }
        (n, cur, tgt)
    } else if mutation_kind == 8 && n > 1 {
        // shrink: remove last element
        let mut cur = current;
        let mut tgt = target;
        cur.pop();
        tgt.pop();
        (n - 1, cur, tgt)
    } else if mutation_kind == 9 && n < 1000 {
        // grow: append digit 0
        let mut cur = current;
        let mut tgt = target;
        cur.push(0u8);
        tgt.push(0u8);
        (n + 1, cur, tgt)
    } else {
        // fallback: identity
        (n, current, target)
    }
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
    let target_count: usize = 100;
    let mut rng = Rng::new(540);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
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

    emit("82195".to_string(), "64723".to_string(), &mut seen, &mut out, &mut count);

    // Edge
    emit("0".to_string(), "0".to_string(), &mut seen, &mut out, &mut count);
    emit("0".to_string(), "5".to_string(), &mut seen, &mut out, &mut count);
    emit("0".to_string(), "9".to_string(), &mut seen, &mut out, &mut count);
    emit("9".to_string(), "0".to_string(), &mut seen, &mut out, &mut count);
    emit("0123456789".to_string(), "9876543210".to_string(), &mut seen, &mut out, &mut count);
    let l1000_a: String = (0..1000).map(|_| '0').collect();
    let l1000_b: String = (0..1000).map(|_| '5').collect();
    emit(l1000_a.clone(), l1000_b.clone(), &mut seen, &mut out, &mut count);
    let l1000_c: String = (0..1000).map(|_| '0').collect();
    let l1000_d: String = (0..1000).map(|_| '0').collect();
    emit(l1000_c, l1000_d, &mut seen, &mut out, &mut count);

    while count < target_count {
        let n = match count % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(2, 20),
            2 => rng.gen_range_usize(20, 100),
            3 => rng.gen_range_usize(100, 500),
            _ => rng.gen_range_usize(500, 1000),
        };
        let cur: String = (0..n).map(|_| (b'0' + rng.gen_range_i64(0, 9) as u8) as char).collect();
        let tgt: String = (0..n).map(|_| (b'0' + rng.gen_range_i64(0, 9) as u8) as char).collect();
        emit(cur, tgt, &mut seen, &mut out, &mut count);
    }
}

