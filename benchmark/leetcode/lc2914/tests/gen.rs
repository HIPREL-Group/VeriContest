use vstd::prelude::*;

verus! {

pub fn generate_test_case(chars: Vec<char>, mutation_kind: u8) -> (result: Vec<char>)
    requires
        2 <= chars.len() <= 100_000,
        chars.len() % 2 == 0,
        forall|i: int| 0 <= i < chars.len() ==> chars[i] == '0' || chars[i] == '1',
    ensures
        2 <= result@.len() <= 100_000,
        result@.len() % 2 == 0,
        forall|i: int| 0 <= i < result@.len() ==> result@[i] == '0' || result@[i] == '1',
{
    if mutation_kind == 0 {
        // identity
        chars
    } else if mutation_kind == 1 {
        // flip first char
        let mut c = chars;
        let v = if c[0] == '0' { '1' } else { '0' };
        c.set(0, v);
        c
    } else if mutation_kind == 2 {
        // flip last char
        let mut c = chars;
        let last = c.len() - 1;
        let v = if c[last] == '0' { '1' } else { '0' };
        c.set(last, v);
        c
    } else if mutation_kind == 3 {
        // set all chars to '0'
        let mut c = chars;
        let mut i: usize = 0;
        while i < c.len()
            invariant
                0 <= i <= c.len(),
                c.len() == chars.len(),
                2 <= c.len() <= 100_000,
                c.len() % 2 == 0,
                forall|j: int| 0 <= j < i ==> c[j] == '0',
                forall|j: int| i <= j < c.len() ==> c[j] == '0' || c[j] == '1',
            decreases c.len() - i,
        {
            c.set(i, '0');
            i += 1;
        }
        c
    } else if mutation_kind == 4 {
        // set all chars to '1'
        let mut c = chars;
        let mut i: usize = 0;
        while i < c.len()
            invariant
                0 <= i <= c.len(),
                c.len() == chars.len(),
                2 <= c.len() <= 100_000,
                c.len() % 2 == 0,
                forall|j: int| 0 <= j < i ==> c[j] == '1',
                forall|j: int| i <= j < c.len() ==> c[j] == '0' || c[j] == '1',
            decreases c.len() - i,
        {
            c.set(i, '1');
            i += 1;
        }
        c
    } else if mutation_kind == 5 && chars.len() <= 99_998 {
        // grow by 2 (push '0', '0')
        let mut c = chars;
        c.push('0');
        c.push('0');
        c
    } else if mutation_kind == 6 && chars.len() > 2 {
        // shrink by 2 (pop twice)
        let mut c = chars;
        c.pop();
        c.pop();
        c
    } else if mutation_kind == 7 {
        // make first pair identical (both '0')
        let mut c = chars;
        c.set(0, '0');
        c.set(1, '0');
        c
    } else if mutation_kind == 8 {
        // make first pair identical (both '1')
        let mut c = chars;
        c.set(0, '1');
        c.set(1, '1');
        c
    } else if mutation_kind == 9 {
        // make first pair mismatched ('0', '1')
        let mut c = chars;
        c.set(0, '0');
        c.set(1, '1');
        c
    } else if mutation_kind == 10 {
        // flip all chars (invert)
        let mut c = chars;
        let mut i: usize = 0;
        while i < c.len()
            invariant
                0 <= i <= c.len(),
                c.len() == chars.len(),
                2 <= c.len() <= 100_000,
                c.len() % 2 == 0,
                forall|j: int| 0 <= j < i ==> (c[j] == '0' || c[j] == '1'),
                forall|j: int| i <= j < c.len() ==> c[j] == '0' || c[j] == '1',
            decreases c.len() - i,
        {
            let v = if c[i] == '0' { '1' } else { '0' };
            c.set(i, v);
            i += 1;
        }
        c
    } else {
        // fallback: identity
        chars
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

fn mutate(chars: Vec<char>, mutation_kind: u8) -> Vec<char> {
    generate_test_case(chars, mutation_kind)
}

fn random_binary_chars(rng: &mut Rng, len: usize) -> Vec<char> {
    let mut chars = Vec::with_capacity(len);
    for _ in 0..len {
        chars.push(if rng.gen_range_usize(0, 1) == 0 { '0' } else { '1' });
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
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2914);
    let count_target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |chars: Vec<char>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= count_target {
            return;
        }
        let s = chars_to_string(&chars);
        if !seen.insert(s.clone()) {
            return;
        }
        let output = Solution::min_changes(s.clone());
        writeln!(out, "{}", json!({"input": {"s": s}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from the problem description
    let examples: Vec<Vec<char>> = vec![
        vec!['1', '0', '0', '1'],           // "1001" -> 2
        vec!['1', '0'],                      // "10" -> 1
        vec!['0', '0', '0', '0'],            // "0000" -> 0
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

    // Apply every mutation to every example
    for ex in &examples {
        for &mk in &mutation_kinds {
            let result = mutate(ex.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Interesting seed arrays
    let special_seeds: Vec<Vec<char>> = vec![
        vec!['0', '0'],                               // min length, all 0
        vec!['1', '1'],                               // min length, all 1
        vec!['0', '1'],                               // min length, mismatch
        vec!['1', '0'],                               // min length, mismatch
        vec!['1', '1', '0', '0'],                     // beautiful already
        vec!['0', '1', '1', '0'],                     // 2 changes needed
        vec!['0', '1', '0', '1', '0', '1'],           // alternating
        vec!['1', '0', '1', '0', '1', '0'],           // alternating reversed
        vec!['0', '0', '1', '1', '0', '0', '1', '1'], // beautiful
        vec!['0', '1', '1', '0', '0', '1', '1', '0'], // all pairs mismatch
    ];

    for seed_arr in &special_seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed_arr.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with diverse size classes and random mutations
    while count < count_target {
        let half_n: usize = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),           // tiny (len 2-6)
            1 => rng.gen_range_usize(1, 10),           // small (len 2-20)
            2 => rng.gen_range_usize(11, 100),         // medium (len 22-200)
            3 => rng.gen_range_usize(101, 1000),       // large (len 202-2000)
            _ => rng.gen_range_usize(1001, 5000),      // very large
        };
        let n = half_n * 2; // ensure even length
        let sv = random_binary_chars(&mut rng, n);
        let mk = rng.gen_range_usize(0, 10) as u8;
        let result = mutate(sv, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
