use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    s0: i32, s1: i32, s2: i32, s3: i32, s4: i32, s5: i32,
    mutation_kind: u8,
) -> (result: Vec<i32>)
    requires
        1 <= s0 <= 9,
        1 <= s1 <= 9,
        1 <= s2 <= 9,
        1 <= s3 <= 9,
        1 <= s4 <= 9,
        1 <= s5 <= 9,
    ensures
        result.len() == 6,
        forall|i: int| 0 <= i < 6 ==> 1 <= #[trigger] result@[i] as int <= 9,
{
    let mut sticks: Vec<i32> = Vec::new();
    sticks.push(s0);
    sticks.push(s1);
    sticks.push(s2);
    sticks.push(s3);
    sticks.push(s4);
    sticks.push(s5);

    assert(sticks@[0] == s0) by {}
    assert(sticks@[1] == s1) by {}
    assert(sticks@[2] == s2) by {}
    assert(sticks@[3] == s3) by {}
    assert(sticks@[4] == s4) by {}
    assert(sticks@[5] == s5) by {}

    if mutation_kind == 0 {
        // identity
        sticks
    } else if mutation_kind == 1 {
        // set all sticks to s0 (all same length)
        sticks.set(1, s0);
        sticks.set(2, s0);
        sticks.set(3, s0);
        sticks.set(4, s0);
        sticks.set(5, s0);
        assert(sticks@[0] == s0) by {}
        assert(sticks@[1] == s0) by {}
        assert(sticks@[2] == s0) by {}
        assert(sticks@[3] == s0) by {}
        assert(sticks@[4] == s0) by {}
        assert(sticks@[5] == s0) by {}
        sticks
    } else if mutation_kind == 2 {
        // four legs same (s0), two heads same (s1) -> elephant
        sticks.set(0, s0);
        sticks.set(1, s0);
        sticks.set(2, s0);
        sticks.set(3, s0);
        sticks.set(4, s1);
        sticks.set(5, s1);
        assert(sticks@[0] == s0) by {}
        assert(sticks@[1] == s0) by {}
        assert(sticks@[2] == s0) by {}
        assert(sticks@[3] == s0) by {}
        assert(sticks@[4] == s1) by {}
        assert(sticks@[5] == s1) by {}
        sticks
    } else if mutation_kind == 3 {
        // four legs same (s0), two heads different (s1, s2) -> bear
        sticks.set(0, s0);
        sticks.set(1, s0);
        sticks.set(2, s0);
        sticks.set(3, s0);
        sticks.set(4, s1);
        sticks.set(5, s2);
        assert(sticks@[0] == s0) by {}
        assert(sticks@[1] == s0) by {}
        assert(sticks@[2] == s0) by {}
        assert(sticks@[3] == s0) by {}
        assert(sticks@[4] == s1) by {}
        assert(sticks@[5] == s2) by {}
        sticks
    } else if mutation_kind == 4 {
        // five same (s0) + one different (s1)
        sticks.set(0, s0);
        sticks.set(1, s0);
        sticks.set(2, s0);
        sticks.set(3, s0);
        sticks.set(4, s0);
        sticks.set(5, s1);
        assert(sticks@[0] == s0) by {}
        assert(sticks@[1] == s0) by {}
        assert(sticks@[2] == s0) by {}
        assert(sticks@[3] == s0) by {}
        assert(sticks@[4] == s0) by {}
        assert(sticks@[5] == s1) by {}
        sticks
    } else if mutation_kind == 5 {
        // all boundary value 1
        sticks.set(0, 1);
        sticks.set(1, 1);
        sticks.set(2, 1);
        sticks.set(3, 1);
        sticks.set(4, 1);
        sticks.set(5, 1);
        assert(sticks@[0] == 1i32) by {}
        assert(sticks@[1] == 1i32) by {}
        assert(sticks@[2] == 1i32) by {}
        assert(sticks@[3] == 1i32) by {}
        assert(sticks@[4] == 1i32) by {}
        assert(sticks@[5] == 1i32) by {}
        sticks
    } else if mutation_kind == 6 {
        // all boundary value 9
        sticks.set(0, 9);
        sticks.set(1, 9);
        sticks.set(2, 9);
        sticks.set(3, 9);
        sticks.set(4, 9);
        sticks.set(5, 9);
        assert(sticks@[0] == 9i32) by {}
        assert(sticks@[1] == 9i32) by {}
        assert(sticks@[2] == 9i32) by {}
        assert(sticks@[3] == 9i32) by {}
        assert(sticks@[4] == 9i32) by {}
        assert(sticks@[5] == 9i32) by {}
        sticks
    } else if mutation_kind == 7 {
        // swap first and last
        sticks.set(0, s5);
        sticks.set(5, s0);
        assert(sticks@[0] == s5) by {}
        assert(sticks@[1] == s1) by {}
        assert(sticks@[2] == s2) by {}
        assert(sticks@[3] == s3) by {}
        assert(sticks@[4] == s4) by {}
        assert(sticks@[5] == s0) by {}
        sticks
    } else {
        // fallback: identity
        sticks
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

fn build_input(sticks: &[i32]) -> String {
    let parts: Vec<String> = sticks.iter().map(|x| x.to_string()).collect();
    format!("{}\n", parts.join(" "))
}

fn build_output(r: i32) -> String {
    if r == 1 { "Bear\n".to_string() }
    else if r == 2 { "Elephant\n".to_string() }
    else { "Alien\n".to_string() }
}

// Check if input violates "you cannot make both animals" guarantee.
// We must skip those (would produce "Both" undefined cases).
// Both possible: have 4+ of one length, AND remaining could be both bear and elephant
// Since the input has exactly 6 sticks, having 4+ of a length means the remaining 2 sticks
// are determined. If those 2 are equal, only Elephant is possible. If different, only Bear.
// 5+ of a length: bear (since head < body or head == body, but we have e.g. four legs of L
//   and two more sticks of length L and X, so head=L, body=X. If X != L, bear; if X == L, both possible? but this means 6 of L which is Elephant)
// So 5 of L and one X<>L means head=L, body=X. If X != L, only Bear. So no ambiguity.
// Actually input always has unambiguous answer, so skip nothing.

fn main() {
    let target_count: usize = 100;
    let mut rng = Rng::new(471);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |sticks: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        let key = format!("{:?}", sticks);
        if !seen.insert(key) { return; }
        let result = Solution::animal_type(sticks.clone());
        let inp = build_input(&sticks);
        let outp = build_output(result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // Examples
    emit(vec![4, 2, 5, 4, 4, 4], &mut seen, &mut out, &mut count);
    emit(vec![4, 4, 5, 4, 4, 5], &mut seen, &mut out, &mut count);
    emit(vec![1, 2, 3, 4, 5, 6], &mut seen, &mut out, &mut count);

    // Edge cases
    // All same -> Elephant (6 of L)
    emit(vec![5, 5, 5, 5, 5, 5], &mut seen, &mut out, &mut count);
    emit(vec![1, 1, 1, 1, 1, 1], &mut seen, &mut out, &mut count);
    emit(vec![9, 9, 9, 9, 9, 9], &mut seen, &mut out, &mut count);
    // 5 of L + 1 different -> Bear
    emit(vec![1, 1, 1, 1, 1, 9], &mut seen, &mut out, &mut count);
    emit(vec![3, 3, 3, 3, 3, 1], &mut seen, &mut out, &mut count);
    // 4 of L + 2 equal but different -> Elephant
    emit(vec![2, 2, 2, 2, 5, 5], &mut seen, &mut out, &mut count);
    emit(vec![1, 1, 1, 1, 9, 9], &mut seen, &mut out, &mut count);
    // 4 of L + 2 different -> Bear
    emit(vec![3, 3, 3, 3, 1, 5], &mut seen, &mut out, &mut count);
    // 3 of L max -> Alien
    emit(vec![1, 1, 1, 2, 2, 3], &mut seen, &mut out, &mut count);

    // Random; need to ensure the input doesn't violate "cannot make both" guarantee
    // Actually with exactly 6 sticks the answer is uniquely determined by counts, so no issue.
    while count < target_count {
        let mut sticks = Vec::with_capacity(6);
        for _ in 0..6 {
            sticks.push(rng.gen_range_i64(1, 9) as i32);
        }
        emit(sticks, &mut seen, &mut out, &mut count);
    }
}

