use vstd::prelude::*;

verus! {

pub open spec fn valid_latin(c: u8) -> bool {
    (c >= 65u8 && c <= 90u8) || (c >= 97u8 && c <= 122u8)
}

pub fn generate_test_case(n: usize, chars: &Vec<u8>) -> (s: Vec<u8>)
    requires
        1 <= n <= 100,
        chars.len() == n,
        forall|i: int| 0 <= i < chars.len() ==> valid_latin(#[trigger] chars[i]),
    ensures
        s.len() == n,
        1 <= n <= 100,
        forall|u: int| 0 <= u < n as int ==> valid_latin(#[trigger] s[u]),
{
    let mut s: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            s.len() == i,
            chars.len() == n,
            1 <= n <= 100,
            forall|k: int| 0 <= k < chars.len() ==> valid_latin(#[trigger] chars[k]),
            forall|k: int| 0 <= k < i as int ==> s[k] == chars[k],
            forall|k: int| 0 <= k < i as int ==> valid_latin(#[trigger] s[k]),
        decreases n - i,
    {
        s.push(chars[i]);
        i = i + 1;
    }
    s
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
    let mut rng = Rng::new(52004);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |s: String, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        let n = s.len();
        if n < 1 || n > 100 { return; }
        for c in s.chars() {
            if !c.is_ascii_alphabetic() { return; }
        }
        if !seen.insert(s.clone()) { return; }
        let bytes: Vec<u8> = s.bytes().collect();
        let result = Solution::is_pangram(n, bytes);
        let inp = format!("{}\n{}\n", n, s);
        let outp = if result { "YES\n".to_string() } else { "NO\n".to_string() };
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // Adversarial: all 26 single chars
    for c in b'a'..=b'z' {
        emit((c as char).to_string(), &mut seen, &mut out, &mut count);
    }
    for c in b'A'..=b'Z' {
        emit((c as char).to_string(), &mut seen, &mut out, &mut count);
    }

    // Pangrams with various length
    let pangram_base = "abcdefghijklmnopqrstuvwxyz";
    emit(pangram_base.to_string(), &mut seen, &mut out, &mut count);
    emit(pangram_base.to_uppercase(), &mut seen, &mut out, &mut count);
    // Mixed case pangram
    let mut mixed: String = String::new();
    for (i, c) in pangram_base.chars().enumerate() {
        if i % 2 == 0 {
            mixed.push(c.to_ascii_uppercase());
        } else {
            mixed.push(c);
        }
    }
    emit(mixed, &mut seen, &mut out, &mut count);

    // Missing exactly 1 letter (each)
    for missing_idx in 0..26 {
        let mut s = String::new();
        for i in 0..26 {
            if i == missing_idx { continue; }
            s.push((b'a' + i) as char);
        }
        emit(s.clone(), &mut seen, &mut out, &mut count);
        // Pad to 50
        let mut s2 = s.clone();
        while s2.len() < 50 {
            s2.push('a');
        }
        emit(s2, &mut seen, &mut out, &mut count);
    }

    // 100 chars, all same letter (each letter)
    for c in b'a'..=b'z' {
        let s: String = std::iter::repeat(c as char).take(100).collect();
        emit(s, &mut seen, &mut out, &mut count);
    }

    // Random
    while count < target_count {
        let n = rng.gen_range_usize(1, 100);
        let mut s = String::new();
        if count % 2 == 0 {
            for _ in 0..n {
                let r = rng.gen_range_i64(0, 51) as u8;
                let c = if r < 26 { b'a' + r } else { b'A' + (r - 26) };
                s.push(c as char);
            }
        } else if n >= 26 {
            for c in b'a'..=b'z' { s.push(c as char); }
            while s.len() < n {
                let r = rng.gen_range_i64(0, 51) as u8;
                let c = if r < 26 { b'a' + r } else { b'A' + (r - 26) };
                s.push(c as char);
            }
            let mut sb: Vec<char> = s.chars().collect();
            for k in (1..sb.len()).rev() {
                let j = rng.gen_range_usize(0, k);
                sb.swap(k, j);
            }
            s = sb.iter().collect();
        } else {
            // random non-pangram
            for _ in 0..n {
                let r = rng.gen_range_i64(0, 5) as u8;
                s.push((b'a' + r) as char);
            }
        }
        emit(s, &mut seen, &mut out, &mut count);
    }
}

