use vstd::prelude::*;
use vstd::string::*;

verus! {

pub open spec fn is_lowercase_word(s: Seq<char>) -> bool {
    forall |i: int| 0 <= i < s.len() ==> 97 <= (#[trigger] s[i] as u32) && (s[i] as u32) <= 122
}

pub fn generate_test_case(words: Vec<String>, chars: String, mutation_kind: u8) -> (result: (Vec<String>, String))
    requires
        1 <= words.len() <= 1000,
        1 <= chars@.len() <= 100,
        is_lowercase_word(chars@),
        forall |i: int| 0 <= i < words.len() ==> 1 <= #[trigger] words[i]@.len() <= 100 && is_lowercase_word(words[i]@),
    ensures
        1 <= result.0.len() <= 1000,
        1 <= result.1@.len() <= 100,
        is_lowercase_word(result.1@),
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i]@.len() <= 100 && is_lowercase_word(result.0[i]@),
{
    if mutation_kind == 0 {
        // identity
        (words, chars)
    } else if mutation_kind == 1 && words.len() > 1 {
        // remove last word
        let mut w = words;
        w.pop();
        (w, chars)
    } else {
        // fallback: identity
        (words, chars)
    }
}

} // verus!

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

extern crate serde_json;
use serde_json::json;

fn random_lowercase_string(rng: &mut Rng, len: usize) -> String {
    let mut s = String::new();
    for _ in 0..len {
        let c = (97 + rng.gen_range_usize(0, 25)) as u8 as char;
        s.push(c);
    }
    s
}

fn main() {
    use std::io::Write;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut emitted = 0usize;

    let mut emit = |words: Vec<String>, chars: String,
                    out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count { return; }
        let output = Solution::count_characters(words.clone(), chars.clone());
        writeln!(out, "{}", json!({
            "input": {"words": words, "chars": chars},
            "output": output
        })).unwrap();
        *emitted += 1;
    };

    // Example 1
    emit(
        vec!["cat".to_string(), "bt".to_string(), "hat".to_string(), "tree".to_string()],
        "atach".to_string(),
        &mut out, &mut emitted,
    );

    // Example 2
    emit(
        vec!["hello".to_string(), "world".to_string(), "leetcode".to_string()],
        "welldonehoneyr".to_string(),
        &mut out, &mut emitted,
    );

    // Edge cases
    emit(vec!["a".to_string()], "a".to_string(), &mut out, &mut emitted);
    emit(vec!["ab".to_string()], "a".to_string(), &mut out, &mut emitted);
    emit(vec!["aaa".to_string(), "aa".to_string()], "aaaa".to_string(), &mut out, &mut emitted);
    emit(vec!["z".to_string()], "z".to_string(), &mut out, &mut emitted);
    emit(
        vec!["abc".to_string(), "def".to_string(), "ghi".to_string()],
        "abcdefghi".to_string(),
        &mut out, &mut emitted,
    );

    // Random test cases with diverse sizes and mutations
    while emitted < count {
        let num_words = match emitted % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 50),
            3 => rng.gen_range_usize(51, 200),
            _ => rng.gen_range_usize(201, 1000),
        };
        let chars_len = match emitted % 4 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 26),
            2 => rng.gen_range_usize(26, 50),
            _ => rng.gen_range_usize(50, 100),
        };
        let chars_str = random_lowercase_string(&mut rng, chars_len);

        let mut words = Vec::new();
        for _ in 0..num_words {
            let word_len = match rng.gen_range_usize(0, 4) {
                0 => 1,
                1 => rng.gen_range_usize(1, 5),
                2 => rng.gen_range_usize(1, 20),
                3 => rng.gen_range_usize(20, 50),
                _ => rng.gen_range_usize(50, 100),
            };
            words.push(random_lowercase_string(&mut rng, word_len));
        }

        let mutation_kind = rng.gen_range_usize(0, 1) as u8;
        let (words, chars_str) = generate_test_case(words, chars_str, mutation_kind);
        emit(words, chars_str, &mut out, &mut emitted);
    }
}
