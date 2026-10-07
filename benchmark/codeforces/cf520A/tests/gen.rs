use vstd::prelude::*;

verus! {

// Spec fn helper copied from spec.rs
pub open spec fn valid_latin(c: u8) -> bool {
    (c >= 65u8 && c <= 90u8) || (c >= 97u8 && c <= 122u8)
}

pub fn generate_test_case(
    chars: Vec<u8>,
    mutation_kind: u8,
) -> (result: (usize, Vec<u8>))
    requires
        1 <= chars.len() <= 100,
        forall|u: int| 0 <= u < chars.len() as int ==> valid_latin(#[trigger] chars[u]),
    ensures
        1 <= result.0 <= 100,
        result.0 == result.1.len(),
        forall|u: int|
            0 <= u < result.0 as int ==> valid_latin(#[trigger] result.1[u]),
{
    let n = chars.len();
    if mutation_kind == 0 {
        // identity
        (n, chars)
    } else if mutation_kind == 1 {
        // set last char to 'A' (65)
        let mut s = chars;
        let last = s.len() - 1;
        s.set(last, 65u8);
        (n, s)
    } else if mutation_kind == 2 {
        // set last char to 'z' (122)
        let mut s = chars;
        let last = s.len() - 1;
        s.set(last, 122u8);
        (n, s)
    } else if mutation_kind == 3 {
        // set first char to 'Z' (90)
        let mut s = chars;
        s.set(0, 90u8);
        (n, s)
    } else if mutation_kind == 4 {
        // set first char to 'a' (97)
        let mut s = chars;
        s.set(0, 97u8);
        (n, s)
    } else if mutation_kind == 5 && chars.len() < 100 {
        // grow by one char (push 'A')
        let mut s = chars;
        s.push(65u8);
        let new_n = s.len();
        (new_n, s)
    } else if mutation_kind == 6 && chars.len() > 1 {
        // shrink by one char (pop)
        let mut s = chars;
        s.pop();
        let new_n = s.len();
        (new_n, s)
    } else if mutation_kind == 7 {
        // set all to 'a' (97) — all same lowercase
        let mut s = chars;
        let mut i: usize = 0;
        while i < s.len()
            invariant
                0 <= i <= s.len(),
                s.len() == n,
                1 <= n <= 100,
                forall|j: int| 0 <= j < i as int ==> #[trigger] s[j] == 97u8,
                forall|j: int| i as int <= j < s.len() as int ==> valid_latin(#[trigger] s[j]),
            decreases s.len() - i,
        {
            s.set(i, 97u8);
            i += 1;
        }
        assert forall|u: int| 0 <= u < n as int implies valid_latin(#[trigger] s[u]) by {
            assert(s[u] == 97u8);
        }
        (n, s)
    } else if mutation_kind == 8 {
        // toggle case of first char
        let mut s = chars;
        let c = s[0];
        if c >= 65u8 && c <= 90u8 {
            s.set(0, (c + 32u8) as u8);
        } else {
            s.set(0, (c - 32u8) as u8);
        }
        (n, s)
    } else if mutation_kind == 9 && chars.len() >= 2 {
        // swap first two chars
        let mut s = chars;
        let tmp = s[0];
        s.set(0, s[1]);
        s.set(1, tmp);
        (n, s)
    } else if mutation_kind == 10 {
        // set all to distinct letters (fill with 'A'..'Z' cycling)
        let mut s = chars;
        let mut i: usize = 0;
        while i < s.len()
            invariant
                0 <= i <= s.len(),
                s.len() == n,
                1 <= n <= 100,
                forall|j: int| 0 <= j < i as int ==> valid_latin(#[trigger] s[j]),
                forall|j: int| i as int <= j < s.len() as int ==> valid_latin(#[trigger] s[j]),
            decreases s.len() - i,
        {
            s.set(i, (65u8 + (i % 26) as u8) as u8);
            i += 1;
        }
        (n, s)
    } else {
        // fallback: identity
        (n, chars)
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

fn random_letter(rng: &mut Rng) -> u8 {
    let r = rng.gen_range_i64(0, 51) as u8;
    if r < 26 {
        b'a' + r
    } else {
        b'A' + (r - 26)
    }
}

fn main() {
    let target_count: usize = 100;
    let mut rng = Rng::new(520);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
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

    emit("toosmallword".to_string(), &mut seen, &mut out, &mut count);
    emit("TheQuickBrownFoxJumpsOverTheLazyDog".to_string(), &mut seen, &mut out, &mut count);

    // Edge: minimal & all letters
    emit("a".to_string(), &mut seen, &mut out, &mut count);
    emit("Z".to_string(), &mut seen, &mut out, &mut count);
    emit("abcdefghijklmnopqrstuvwxyz".to_string(), &mut seen, &mut out, &mut count);
    emit("ABCDEFGHIJKLMNOPQRSTUVWXYZ".to_string(), &mut seen, &mut out, &mut count);
    emit("abcdefghijklmnopqrstuvwxy".to_string(), &mut seen, &mut out, &mut count); // missing z
    emit("AbCdEfGhIjKlMnOpQrStUvWxYz".to_string(), &mut seen, &mut out, &mut count);
    // Length 100
    let mut s100 = String::new();
    for _ in 0..100 { s100.push('a'); }
    emit(s100.clone(), &mut seen, &mut out, &mut count);
    let mut s100b = String::new();
    s100b.push_str("abcdefghijklmnopqrstuvwxyz");
    while s100b.len() < 100 { s100b.push('a'); }
    emit(s100b, &mut seen, &mut out, &mut count);

    while count < target_count {
        let n = rng.gen_range_usize(1, 100);
        let mut s = String::new();
        if count % 3 == 0 {
            // Try to make pangram if n>=26
            if n >= 26 {
                let alphabet: Vec<u8> = (0..26).map(|i| b'a' + i).collect();
                for &c in alphabet.iter() {
                    s.push(c as char);
                }
                while s.len() < n {
                    s.push(random_letter(&mut rng) as char);
                }
                // Shuffle for adversarial-ness
                let mut sb: Vec<char> = s.chars().collect();
                for k in (1..sb.len()).rev() {
                    let j = rng.gen_range_usize(0, k);
                    sb.swap(k, j);
                }
                s = sb.iter().collect();
            } else {
                for _ in 0..n {
                    s.push(random_letter(&mut rng) as char);
                }
            }
        } else {
            for _ in 0..n {
                s.push(random_letter(&mut rng) as char);
            }
        }
        emit(s, &mut seen, &mut out, &mut count);
    }
}

