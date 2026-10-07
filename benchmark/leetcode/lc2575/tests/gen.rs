use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    chars: Vec<char>,
    m: i32,
    mutation_kind: u8,
) -> (result: (Vec<char>, i32))
    requires
        1 <= chars.len() <= 100000,
        forall|i: int| 0 <= i < chars.len() ==> '0' <= #[trigger] chars[i] <= '9',
        1 <= m <= 1000000000,
    ensures
        1 <= result.0@.len() <= 100000,
        1 <= result.1 <= 1000000000,
        forall|i: int| 0 <= i < result.0@.len() ==> '0' <= #[trigger] result.0@[i] <= '9',
{
    if mutation_kind == 0 {
        // identity
        (chars, m)
    } else if mutation_kind == 1 {
        // set last digit to '9'
        let mut d = chars;
        let last = d.len() - 1;
        d.set(last, '9');
        (d, m)
    } else if mutation_kind == 2 {
        // set all digits to '0'
        let mut d = chars;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == chars.len(),
                1 <= d.len() <= 100000,
                forall|j: int| 0 <= j < i ==> d[j] == '0',
                forall|j: int| i <= j < d.len() ==> d[j] == chars[j],
                forall|j: int| 0 <= j < i ==> '0' <= #[trigger] d[j] <= '9',
                forall|j: int| i <= j < d.len() ==> '0' <= #[trigger] d[j] <= '9',
            decreases d.len() - i,
        {
            d.set(i, '0');
            i += 1;
        }
        (d, m)
    } else if mutation_kind == 3 && chars.len() < 100000 {
        // grow: append '0'
        let mut d = chars;
        d.push('0');
        (d, m)
    } else if mutation_kind == 4 && chars.len() > 1 {
        // shrink: remove last
        let mut d = chars;
        d.pop();
        (d, m)
    } else if mutation_kind == 5 {
        // nudge last digit up
        let mut d = chars;
        let last = d.len() - 1;
        if d[last] < '9' {
            d.set(last, ((d[last] as u8) + 1) as char);
            assert('0' <= d[last as int] <= '9') by {
                // The old char was in '0'..'8', so +1 gives '1'..'9'
            }
        }
        (d, m)
    } else if mutation_kind == 6 {
        // nudge last digit down
        let mut d = chars;
        let last = d.len() - 1;
        if d[last] > '0' {
            d.set(last, ((d[last] as u8) - 1) as char);
            assert('0' <= d[last as int] <= '9') by {
                // The old char was in '1'..'9', so -1 gives '0'..'8'
            }
        }
        (d, m)
    } else if mutation_kind == 7 {
        // set m to 1 (boundary)
        (chars, 1)
    } else if mutation_kind == 8 {
        // set m to max boundary
        (chars, 1_000_000_000)
    } else if mutation_kind == 9 {
        // set all digits to '9'
        let mut d = chars;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == chars.len(),
                1 <= d.len() <= 100000,
                forall|j: int| 0 <= j < i ==> d[j] == '9',
                forall|j: int| i <= j < d.len() ==> d[j] == chars[j],
                forall|j: int| 0 <= j < i ==> '0' <= #[trigger] d[j] <= '9',
                forall|j: int| i <= j < d.len() ==> '0' <= #[trigger] d[j] <= '9',
            decreases d.len() - i,
        {
            d.set(i, '9');
            i += 1;
        }
        (d, m)
    } else if mutation_kind == 10 {
        // set last digit to '0'
        let mut d = chars;
        let last = d.len() - 1;
        d.set(last, '0');
        (d, m)
    } else {
        // fallback: identity
        (chars, m)
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

struct Solution;
include!("../code.rs");

fn random_digit_chars(rng: &mut Rng, len: usize) -> Vec<char> {
    let mut chars = Vec::with_capacity(len);
    for _ in 0..len {
        chars.push((b'0' + rng.gen_range_usize(0, 9) as u8) as char);
    }
    chars
}

fn chars_to_string(chars: &[char]) -> String {
    chars.iter().collect()
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);

    let mut rng = Rng::new(seed);
    let mut generated = 0usize;

    // Example inputs from description.md
    let examples: Vec<(Vec<char>, i32)> = vec![
        ("998244353".chars().collect(), 3),
        ("1010".chars().collect(), 10),
    ];

    for (ex_chars, ex_m) in &examples {
        let (word_chars, m_val) = generate_test_case(ex_chars.clone(), *ex_m, 0);
        let word_str = chars_to_string(&word_chars);
        let output = Solution::divisibility_array(word_str.clone(), m_val);
        writeln!(out, "{}", json!({
            "input": {"word": word_str, "m": m_val},
            "output": output
        })).unwrap();
        generated += 1;
    }

    let num_mutations: u8 = 11;

    while generated < count {
        // Size classes for word length
        let n: usize = match generated % 5 {
            0 => rng.gen_range_usize(1, 5),          // tiny
            1 => rng.gen_range_usize(1, 10),         // small
            2 => rng.gen_range_usize(11, 100),       // medium
            3 => rng.gen_range_usize(101, 1000),     // large
            _ => rng.gen_range_usize(1001, 10000),   // big (cap for speed)
        };

        let chars = random_digit_chars(&mut rng, n);

        // m value with boundary mixing
        let m: i32 = if generated % 5 == 0 {
            *[1i32, 2, 10, 1_000_000_000, 999_999_999]
                .get(rng.gen_range_usize(0, 4))
                .unwrap()
        } else {
            rng.gen_range_i64(1, 1_000_000_000) as i32
        };

        let mutation = (generated % num_mutations as usize) as u8;
        let (word_chars, m_val) = generate_test_case(chars, m, mutation);
        let word_str = chars_to_string(&word_chars);
        let output = Solution::divisibility_array(word_str.clone(), m_val);

        writeln!(out, "{}", json!({
            "input": {"word": word_str, "m": m_val},
            "output": output
        })).unwrap();
        generated += 1;
    }

    eprintln!("Generated {} test cases to {:?}", generated, out_path);
}
