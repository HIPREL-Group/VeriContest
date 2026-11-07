use vstd::prelude::*;

verus! {

pub fn generate_test_case(chars: Vec<char>, mutation_kind: u8) -> (result: Vec<char>)
    requires
        1 <= chars.len() <= 100,
        forall |i: int| 0 <= i < chars@.len() ==>
            (('A' <= chars@[i] && chars@[i] <= 'Z') || ('a' <= chars@[i] && chars@[i] <= 'z')),
    ensures
        1 <= result@.len() <= 100,
        forall |i: int| 0 <= i < result@.len() ==>
            (('A' <= result@[i] && result@[i] <= 'Z') || ('a' <= result@[i] && result@[i] <= 'z')),
{
    if mutation_kind == 0 {
        // identity
        chars
    } else if mutation_kind == 1 {
        // set first char to 'A' (uppercase)
        let mut d = chars;
        d.set(0, 'A');
        assert forall |j: int| 0 <= j < d@.len() implies
            (('A' <= d@[j] && d@[j] <= 'Z') || ('a' <= d@[j] && d@[j] <= 'z'))
        by {
            if j == 0 {
            } else {
                assert(d@[j] == chars@[j]);
            }
        }
        d
    } else if mutation_kind == 2 {
        // set first char to 'a' (lowercase)
        let mut d = chars;
        d.set(0, 'a');
        assert forall |j: int| 0 <= j < d@.len() implies
            (('A' <= d@[j] && d@[j] <= 'Z') || ('a' <= d@[j] && d@[j] <= 'z'))
        by {
            if j == 0 {
            } else {
                assert(d@[j] == chars@[j]);
            }
        }
        d
    } else if mutation_kind == 3 {
        // set all to 'A' (all uppercase pattern)
        let mut d = chars;
        let mut idx: usize = 0;
        while idx < d.len()
            invariant
                0 <= idx <= d@.len(),
                d@.len() == chars@.len(),
                1 <= d@.len() <= 100,
                forall |j: int| 0 <= j < idx as int ==> d@[j] == 'A',
                forall |j: int| idx as int <= j < d@.len() ==> d@[j] == chars@[j],
            decreases d@.len() - idx as int,
        {
            d.set(idx, 'A');
            idx += 1;
        }
        assert forall |j: int| 0 <= j < d@.len() implies
            (('A' <= d@[j] && d@[j] <= 'Z') || ('a' <= d@[j] && d@[j] <= 'z'))
        by {
            assert(d@[j] == 'A');
        }
        d
    } else if mutation_kind == 4 {
        // set all to 'a' (all lowercase pattern)
        let mut d = chars;
        let mut idx: usize = 0;
        while idx < d.len()
            invariant
                0 <= idx <= d@.len(),
                d@.len() == chars@.len(),
                1 <= d@.len() <= 100,
                forall |j: int| 0 <= j < idx as int ==> d@[j] == 'a',
                forall |j: int| idx as int <= j < d@.len() ==> d@[j] == chars@[j],
            decreases d@.len() - idx as int,
        {
            d.set(idx, 'a');
            idx += 1;
        }
        assert forall |j: int| 0 <= j < d@.len() implies
            (('A' <= d@[j] && d@[j] <= 'Z') || ('a' <= d@[j] && d@[j] <= 'z'))
        by {
            assert(d@[j] == 'a');
        }
        d
    } else if mutation_kind == 5 && chars.len() < 100 {
        // grow by appending 'a'
        let mut d = chars;
        d.push('a');
        assert forall |j: int| 0 <= j < d@.len() implies
            (('A' <= d@[j] && d@[j] <= 'Z') || ('a' <= d@[j] && d@[j] <= 'z'))
        by {
            if j < chars@.len() as int {
                assert(d@[j] == chars@[j]);
            } else {
                assert(d@[j] == 'a');
            }
        }
        d
    } else if mutation_kind == 6 && chars.len() > 1 {
        // shrink by removing last
        let mut d = chars;
        let _ = d.pop();
        assert forall |j: int| 0 <= j < d@.len() implies
            (('A' <= d@[j] && d@[j] <= 'Z') || ('a' <= d@[j] && d@[j] <= 'z'))
        by {
            assert(d@[j] == chars@[j]);
        }
        d
    } else if mutation_kind == 7 {
        // set last char to 'Z'
        let mut d = chars;
        let last = d.len() - 1;
        d.set(last, 'Z');
        assert forall |j: int| 0 <= j < d@.len() implies
            (('A' <= d@[j] && d@[j] <= 'Z') || ('a' <= d@[j] && d@[j] <= 'z'))
        by {
            if j == last as int {
            } else {
                assert(d@[j] == chars@[j]);
            }
        }
        d
    } else if mutation_kind == 8 {
        // set last char to 'z'
        let mut d = chars;
        let last = d.len() - 1;
        d.set(last, 'z');
        assert forall |j: int| 0 <= j < d@.len() implies
            (('A' <= d@[j] && d@[j] <= 'Z') || ('a' <= d@[j] && d@[j] <= 'z'))
        by {
            if j == last as int {
            } else {
                assert(d@[j] == chars@[j]);
            }
        }
        d
    } else if mutation_kind == 9 && chars.len() >= 2 {
        // title case: first 'G', rest 'o'
        let mut d = chars;
        d.set(0, 'G');
        let mut idx: usize = 1;
        while idx < d.len()
            invariant
                1 <= idx <= d@.len(),
                d@.len() == chars@.len(),
                1 <= d@.len() <= 100,
                d@[0int] == 'G',
                forall |j: int| 1 <= j < idx as int ==> d@[j] == 'o',
                forall |j: int| idx as int <= j < d@.len() ==> d@[j] == chars@[j],
            decreases d@.len() - idx as int,
        {
            d.set(idx, 'o');
            idx += 1;
        }
        assert forall |j: int| 0 <= j < d@.len() implies
            (('A' <= d@[j] && d@[j] <= 'Z') || ('a' <= d@[j] && d@[j] <= 'z'))
        by {
            if j == 0 {
                assert(d@[j] == 'G');
            } else {
                assert(d@[j] == 'o');
            }
        }
        d
    } else {
        // fallback: identity
        chars
    }
}

} // verus!

extern crate serde_json;
use serde_json::json;

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

    fn gen_u8(&mut self) -> u8 {
        (self.next_u64() % 256) as u8
    }
}

fn random_char(rng: &mut Rng, upper: bool) -> char {
    if upper {
        (b'A' + (rng.next_u64() % 26) as u8) as char
    } else {
        (b'a' + (rng.next_u64() % 26) as u8) as char
    }
}

fn random_word(rng: &mut Rng, len: usize, pattern: u8) -> Vec<char> {
    let mut chars = Vec::with_capacity(len);
    for k in 0..len {
        let upper = match pattern {
            0 => true,                          // ALL UPPER
            1 => false,                         // all lower
            2 => k == 0,                        // Title Case
            3 => k != 0,                        // iNVERSE tITLE
            _ => rng.next_u64() % 2 == 0,       // random mix
        };
        chars.push(random_char(rng, upper));
    }
    chars
}

fn detect_capital_use(word: &[char]) -> bool {
    let len = word.len();
    if len == 0 { return false; }

    // All uppercase
    if word.iter().all(|c| c.is_ascii_uppercase()) {
        return true;
    }
    // All lowercase
    if word.iter().all(|c| c.is_ascii_lowercase()) {
        return true;
    }
    // First uppercase, rest lowercase
    if word[0].is_ascii_uppercase() && word[1..].iter().all(|c| c.is_ascii_lowercase()) {
        return true;
    }
    false
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |chars: &Vec<char>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count { return; }
        let word: String = chars.iter().collect();
        if !seen.insert(word.clone()) { return; }
        let output = detect_capital_use(chars);
        writeln!(out, "{}", json!({"input": {"word": word}, "output": output})).unwrap();
        *emitted += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<char>> = vec![
        "USA".chars().collect(),
        "FlaG".chars().collect(),
        "leetcode".chars().collect(),
        "Google".chars().collect(),
    ];
    for ex in &examples {
        let result = generate_test_case(ex.clone(), 0);
        emit(&result, &mut seen, &mut out, &mut emitted);
    }

    // Seed pool with diverse patterns
    let seed_words: Vec<Vec<char>> = vec![
        vec!['A'],
        vec!['a'],
        vec!['Z'],
        vec!['z'],
        vec!['A', 'B', 'C'],
        vec!['a', 'b', 'c'],
        vec!['A', 'b', 'c'],
        vec!['a', 'B', 'c'],
        vec!['A', 'B', 'c'],
        vec!['a', 'b', 'C'],
        vec!['H', 'e', 'l', 'l', 'o'],
        vec!['W', 'O', 'R', 'L', 'D'],
        vec!['h', 'e', 'l', 'l', 'o'],
        vec!['h', 'E', 'L', 'L', 'O'],
    ];

    // Apply all mutation kinds to seed words
    for word in &seed_words {
        for mk in 0..=10u8 {
            if emitted >= count { break; }
            let result = generate_test_case(word.clone(), mk);
            emit(&result, &mut seen, &mut out, &mut emitted);
        }
        if emitted >= count { break; }
    }

    // Random words with various patterns and mutations
    let patterns: Vec<u8> = vec![0, 1, 2, 3, 4, 4, 4];
    while emitted < count {
        let len = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),       // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 50),      // medium
            3 => rng.gen_range_usize(51, 100),     // large
            _ => 100,                               // max
        };
        let pat = patterns[rng.gen_range_usize(0, patterns.len() - 1)];
        let word = random_word(&mut rng, len, pat);
        let mk = rng.gen_u8() % 11;
        let result = generate_test_case(word, mk);
        emit(&result, &mut seen, &mut out, &mut emitted);
    }
}
