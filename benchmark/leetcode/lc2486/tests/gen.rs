use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    s_chars: Vec<char>,
    t_chars: Vec<char>,
    mutation_kind: u8,
) -> (result: (Vec<char>, Vec<char>))
    requires
        1 <= s_chars.len() <= 100000,
        1 <= t_chars.len() <= 100000,
        forall|i: int| 0 <= i < s_chars.len() ==> 'a' <= #[trigger] s_chars[i] <= 'z',
        forall|i: int| 0 <= i < t_chars.len() ==> 'a' <= #[trigger] t_chars[i] <= 'z',
    ensures
        1 <= result.0@.len() <= 100000,
        1 <= result.1@.len() <= 100000,
        forall|i: int| 0 <= i < result.0@.len() ==> 'a' <= #[trigger] result.0@[i] <= 'z',
        forall|i: int| 0 <= i < result.1@.len() ==> 'a' <= #[trigger] result.1@[i] <= 'z',
{
    if mutation_kind == 0 {
        // identity
        (s_chars, t_chars)
    } else if mutation_kind == 1 {
        // set all s chars to 'a'
        let mut s = s_chars;
        let mut i: usize = 0;
        while i < s.len()
            invariant
                0 <= i <= s.len(),
                s.len() == s_chars.len(),
                1 <= s.len() <= 100000,
                forall|j: int| 0 <= j < s.len() ==> 'a' <= #[trigger] s[j] <= 'z',
            decreases s.len() - i,
        {
            s.set(i, 'a');
            i += 1;
        }
        (s, t_chars)
    } else if mutation_kind == 2 {
        // set all t chars to 'a'
        let mut t = t_chars;
        let mut i: usize = 0;
        while i < t.len()
            invariant
                0 <= i <= t.len(),
                t.len() == t_chars.len(),
                1 <= t.len() <= 100000,
                forall|j: int| 0 <= j < t.len() ==> 'a' <= #[trigger] t[j] <= 'z',
            decreases t.len() - i,
        {
            t.set(i, 'a');
            i += 1;
        }
        (s_chars, t)
    } else if mutation_kind == 3 {
        // set first char of s to match first char of t
        let c = t_chars[0];
        let mut s = s_chars;
        s.set(0, c);
        (s, t_chars)
    } else if mutation_kind == 4 {
        // set first char of t to match first char of s
        let c = s_chars[0];
        let mut t = t_chars;
        t.set(0, c);
        (s_chars, t)
    } else if mutation_kind == 5 {
        // set all s chars to 'z'
        let mut s = s_chars;
        let mut i: usize = 0;
        while i < s.len()
            invariant
                0 <= i <= s.len(),
                s.len() == s_chars.len(),
                1 <= s.len() <= 100000,
                forall|j: int| 0 <= j < s.len() ==> 'a' <= #[trigger] s[j] <= 'z',
            decreases s.len() - i,
        {
            s.set(i, 'z');
            i += 1;
        }
        (s, t_chars)
    } else if mutation_kind == 6 {
        // set all t chars to 'z'
        let mut t = t_chars;
        let mut i: usize = 0;
        while i < t.len()
            invariant
                0 <= i <= t.len(),
                t.len() == t_chars.len(),
                1 <= t.len() <= 100000,
                forall|j: int| 0 <= j < t.len() ==> 'a' <= #[trigger] t[j] <= 'z',
            decreases t.len() - i,
        {
            t.set(i, 'z');
            i += 1;
        }
        (s_chars, t)
    } else if mutation_kind == 7 {
        // swap s and t
        (t_chars, s_chars)
    } else {
        // fallback: identity
        (s_chars, t_chars)
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
}

fn random_chars(rng: &mut Rng, len: usize) -> Vec<char> {
    let mut chars = Vec::with_capacity(len);
    for _ in 0..len {
        let offset = rng.gen_range_usize(0, 25);
        chars.push((b'a' + offset as u8) as char);
    }
    chars
}

struct Solution;
include!("../code.rs");

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

    // Example test cases from description.md
    let examples: Vec<(&str, &str)> = vec![
        ("coaching", "coding"),
        ("abcde", "a"),
        ("z", "abcde"),
    ];

    for (s_str, t_str) in &examples {
        if emitted >= count { break; }
        let s = s_str.to_string();
        let t = t_str.to_string();
        let output = Solution::append_characters(s.clone(), t.clone());
        writeln!(out, "{}", json!({"input": {"s": s, "t": t}, "output": output})).unwrap();
        emitted += 1;
    }

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];

    // Seed pool: diverse hand-crafted inputs
    let seed_pairs: Vec<(&str, &str)> = vec![
        ("a", "a"),
        ("a", "z"),
        ("z", "a"),
        ("abcdefghijklmnopqrstuvwxyz", "az"),
        ("aaa", "aaa"),
        ("zzz", "zzz"),
        ("abc", "xyz"),
        ("abcabc", "abc"),
        ("a", "abcde"),
        ("abcde", "e"),
    ];

    // Apply every mutation to every seed pair
    for (s_str, t_str) in &seed_pairs {
        for &mk in &mutation_kinds {
            if emitted >= count { break; }
            let s_chars: Vec<char> = s_str.chars().collect();
            let t_chars: Vec<char> = t_str.chars().collect();
            let (s_res, t_res) = generate_test_case(s_chars, t_chars, mk);
            let s: String = s_res.iter().collect();
            let t: String = t_res.iter().collect();
            let output = Solution::append_characters(s.clone(), t.clone());
            writeln!(out, "{}", json!({"input": {"s": s, "t": t}, "output": output})).unwrap();
            emitted += 1;
        }
    }

    // Random test cases with diverse sizes
    while emitted < count {
        let s_len = match emitted % 5 {
            0 => rng.gen_range_usize(1, 5),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 100),    // medium
            3 => rng.gen_range_usize(101, 1000),  // large
            _ => rng.gen_range_usize(1001, 10000), // max
        };
        let t_len = match (emitted + 2) % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 10000),
        };

        let s_chars = random_chars(&mut rng, s_len);
        let t_chars = random_chars(&mut rng, t_len);
        let mk = mutation_kinds[rng.gen_range_usize(0, mutation_kinds.len() - 1)];
        let (s_res, t_res) = generate_test_case(s_chars, t_chars, mk);
        let s: String = s_res.iter().collect();
        let t: String = t_res.iter().collect();
        let output = Solution::append_characters(s.clone(), t.clone());
        writeln!(out, "{}", json!({"input": {"s": s, "t": t}, "output": output})).unwrap();
        emitted += 1;
    }
}
