use vstd::prelude::*;

verus! {

pub open spec fn is_lowercase_string(s: Seq<char>) -> bool {
    forall |i: int| 0 <= i < s.len() ==> 97 <= (#[trigger] s[i] as u32) && (s[i] as u32) <= 122
}

pub fn generate_test_case(chars: Vec<char>, mutation_kind: u8) -> (result: Vec<char>)
    requires
        1 <= chars.len() <= 100,
        forall|i: int| 0 <= i < chars.len() ==> 97 <= (#[trigger] chars[i] as u32) && (chars[i] as u32) <= 122,
    ensures
        1 <= result@.len() <= 100,
        is_lowercase_string(result@),
{
    if mutation_kind == 0 {
        // identity
        chars
    } else if mutation_kind == 1 && chars.len() >= 2 {
        // swap first two chars
        let mut d = chars;
        let c0 = d[0];
        let c1 = d[1];
        d.set(0, c1);
        d.set(1, c0);
        d
    } else if mutation_kind == 2 && chars.len() >= 2 {
        // reverse
        let mut d = chars;
        let n = d.len();
        let mut i: usize = 0;
        while i < n / 2
            invariant
                0 <= i <= n / 2,
                d.len() == n,
                1 <= n <= 100,
                forall|j: int| 0 <= j < d.len() ==> 97 <= (#[trigger] d[j] as u32) && (d[j] as u32) <= 122,
            decreases n / 2 - i,
        {
            let ci = d[i];
            let cj = d[n - 1 - i];
            d.set(i, cj);
            d.set(n - 1 - i, ci);
            i += 1;
        }
        d
    } else if mutation_kind == 3 {
        // all 'a's
        let n = chars.len();
        let mut s: Vec<char> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                s.len() == i,
                1 <= n <= 100,
                forall|j: int| 0 <= j < s.len() ==> 97 <= (#[trigger] s[j] as u32) && (s[j] as u32) <= 122,
            decreases n - i,
        {
            s.push('a');
            i += 1;
        }
        s
    } else if mutation_kind == 4 {
        // nudge first char (cycle a->b, ..., z->a)
        let mut d = chars;
        let c = d[0];
        let cv = c as u32;
        let new_v: u32 = if cv == 122 { 97 } else { cv + 1 };
        proof {
            assert(97 <= new_v && new_v <= 122);
            assert(new_v <= 255);
        }
        let new_c: char = (new_v as u8) as char;
        d.set(0, new_c);
        d
    } else if mutation_kind == 5 {
        // all 'z's
        let n = chars.len();
        let mut s: Vec<char> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                s.len() == i,
                1 <= n <= 100,
                forall|j: int| 0 <= j < s.len() ==> 97 <= (#[trigger] s[j] as u32) && (s[j] as u32) <= 122,
            decreases n - i,
        {
            s.push('z');
            i += 1;
        }
        s
    } else if mutation_kind == 6 && chars.len() >= 2 {
        // swap last two chars
        let mut d = chars;
        let n = d.len();
        let c0 = d[n - 2];
        let c1 = d[n - 1];
        d.set(n - 2, c1);
        d.set(n - 1, c0);
        d
    } else if mutation_kind == 7 && chars.len() > 1 {
        // shrink by one
        let mut d = chars;
        d.pop();
        d
    } else if mutation_kind == 8 && chars.len() < 100 {
        // grow by one (append 'a')
        let mut d = chars;
        d.push('a');
        d
    } else if mutation_kind == 9 {
        // nudge last char
        let mut d = chars;
        let last = d.len() - 1;
        let c = d[last];
        let cv = c as u32;
        let new_v: u32 = if cv == 122 { 97 } else { cv + 1 };
        proof {
            assert(97 <= new_v && new_v <= 122);
            assert(new_v <= 255);
        }
        let new_c: char = (new_v as u8) as char;
        d.set(last, new_c);
        d
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

impl Solution {
    pub fn residue_prefixes(s: String) -> i32 {
        let bytes = s.as_bytes();
        let n = bytes.len();
        let mut ans: i32 = 0;
        for i in 0..n {
            let mut seen = [false; 26];
            let mut distinct: i32 = 0;
            for p in 0..=i {
                let idx = (bytes[p] - b'a') as usize;
                if !seen[idx] {
                    seen[idx] = true;
                    distinct += 1;
                }
            }
            let residue = ((i + 1) % 3) as i32;
            if distinct == residue {
                ans += 1;
            }
        }
        ans
    }
}

fn mutate(chars: Vec<char>, mutation_kind: u8) -> Vec<char> {
    generate_test_case(chars, mutation_kind)
}

fn random_lowercase_chars(rng: &mut Rng, len: usize) -> Vec<char> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        let c = (b'a' + (rng.gen_range_usize(0, 25) as u8)) as char;
        v.push(c);
    }
    v
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
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3803);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |result_chars: &[char], seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let s_str = chars_to_string(result_chars);
        if !seen.insert(s_str.clone()) {
            return;
        }
        let output = Solution::residue_prefixes(s_str.clone());
        writeln!(out, "{}", json!({"input": {"s": s_str}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<char>> = vec![
        "abc".chars().collect(),
        "dd".chars().collect(),
        "bob".chars().collect(),
    ];
    for ex in &examples {
        emit(ex, &mut seen, &mut out, &mut count);
    }

    // Curated seeds
    let curated_seeds: Vec<Vec<char>> = vec![
        vec!['a'],
        vec!['z'],
        vec!['a', 'b'],
        vec!['a', 'a'],
        vec!['a', 'b', 'c'],
        vec!['a', 'a', 'a'],
        vec!['z', 'z', 'z'],
        "abcdefghijklmnopqrstuvwxyz".chars().collect(),
        "aabbcc".chars().collect(),
        "abcabc".chars().collect(),
        "aaabbbccc".chars().collect(),
        "abcabcabc".chars().collect(),
        vec!['a', 'b', 'c', 'd', 'e', 'f'],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    for seed_chars in &curated_seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed_chars.clone(), mk);
            emit(&result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations across size classes
    while count < target_count {
        let n: usize = match count % 5 {
            0 => rng.gen_range_usize(1, 5),       // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 30),      // medium
            3 => rng.gen_range_usize(31, 70),      // large
            _ => rng.gen_range_usize(71, 100),     // max
        };
        let chars = random_lowercase_chars(&mut rng, n);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = mutate(chars, mk);
        emit(&result, &mut seen, &mut out, &mut count);
    }
}
