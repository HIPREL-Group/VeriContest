use vstd::prelude::*;

verus! {

pub open spec fn is_lowercase_word(s: Seq<char>) -> bool {
    forall |i: int| 0 <= i < s.len() ==> 97 <= (#[trigger] s[i] as u32) && (s[i] as u32) <= 122
}

pub fn generate_test_case(chars: Vec<char>, mutation_kind: u8) -> (result: (Vec<char>, Vec<char>))
    requires
        1 <= chars.len() <= 50_000,
        forall|i: int| 0 <= i < chars.len() ==> 97 <= (#[trigger] chars[i] as u32) && (chars[i] as u32) <= 122,
    ensures
        1 <= result.0@.len() <= 50_000,
        1 <= result.1@.len() <= 50_000,
        is_lowercase_word(result.0@),
        is_lowercase_word(result.1@),
{
    if mutation_kind == 0 {
        let s = chars.clone();
        let t = chars;
        (s, t)
    } else if mutation_kind == 1 && chars.len() >= 2 {
        let s = chars.clone();
        let mut t = chars;
        let c0 = t[0];
        let c1 = t[1];
        t.set(0, c1);
        t.set(1, c0);
        (s, t)
    } else if mutation_kind == 2 && chars.len() >= 2 {
        let s = chars.clone();
        let mut t = chars;
        let n = t.len();
        let mut i: usize = 0;
        while i < n / 2
            invariant
                0 <= i <= n / 2,
                t.len() == n,
                n == s.len(),
                1 <= n <= 50_000,
                forall|j: int| 0 <= j < t.len() ==> 97 <= (#[trigger] t[j] as u32) && (t[j] as u32) <= 122,
            decreases n / 2 - i,
        {
            let ci = t[i];
            let cj = t[n - 1 - i];
            t.set(i, cj);
            t.set(n - 1 - i, ci);
            i += 1;
        }
        (s, t)
    } else if mutation_kind == 3 {
        let n = chars.len();
        let mut s: Vec<char> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                s.len() == i,
                1 <= n <= 50_000,
                forall|j: int| 0 <= j < s.len() ==> 97 <= (#[trigger] s[j] as u32) && (s[j] as u32) <= 122,
            decreases n - i,
        {
            s.push('a');
            i += 1;
        }
        let t = s.clone();
        (s, t)
    } else if mutation_kind == 4 && chars.len() >= 2 {
        let s = chars.clone();
        let mut t = chars;
        let c = t[0];
        let cv = c as u32;
        let new_v: u32 = if cv == 122 { 97 } else { cv + 1 };
        proof {
            assert(97 <= new_v && new_v <= 122);
            assert(new_v <= 255);
        }
        let new_c: char = (new_v as u8) as char;
        t.set(0, new_c);
        (s, t)
    } else if mutation_kind == 5 {
        let n = chars.len();
        let mut s: Vec<char> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                s.len() == i,
                1 <= n <= 50_000,
                forall|j: int| 0 <= j < s.len() ==> 97 <= (#[trigger] s[j] as u32) && (s[j] as u32) <= 122,
            decreases n - i,
        {
            s.push('z');
            i += 1;
        }
        let t = s.clone();
        (s, t)
    } else if mutation_kind == 6 && chars.len() >= 2 {
        let s = chars.clone();
        let mut t = chars;
        let n = t.len();
        let c0 = t[n - 2];
        let c1 = t[n - 1];
        t.set(n - 2, c1);
        t.set(n - 1, c0);
        (s, t)
    } else {
        let s = chars.clone();
        let t = chars;
        (s, t)
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
    pub fn is_anagram(s: String, t: String) -> bool {
        let s_bytes = s.as_bytes();
        let t_bytes = t.as_bytes();
        if s_bytes.len() != t_bytes.len() {
            return false;
        }
        let mut cnt = [0i32; 26];
        for &b in s_bytes {
            cnt[(b - b'a') as usize] += 1;
        }
        for &b in t_bytes {
            cnt[(b - b'a') as usize] -= 1;
        }
        cnt.iter().all(|&c| c == 0)
    }
}

fn mutate(chars: Vec<char>, mutation_kind: u8) -> (Vec<char>, Vec<char>) {
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
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(242);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |s_chars: &[char], t_chars: &[char], seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let s_str = chars_to_string(s_chars);
        let t_str = chars_to_string(t_chars);
        let key = format!("{}|{}", s_str, t_str);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::is_anagram(s_str.clone(), t_str.clone());
        writeln!(out, "{}", json!({"input": {"s": s_str, "t": t_str}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let example_seeds: Vec<(Vec<char>, Vec<char>)> = vec![
        ("anagram".chars().collect(), "nagaram".chars().collect()),
        ("rat".chars().collect(), "car".chars().collect()),
    ];
    for (s, t) in &example_seeds {
        emit(s, t, &mut seen, &mut out, &mut count);
    }

    // Curated seeds
    let curated_seeds: Vec<Vec<char>> = vec![
        vec!['a'],
        vec!['z'],
        vec!['a', 'b'],
        vec!['a', 'b', 'c'],
        vec!['a', 'a', 'a'],
        vec!['z', 'z', 'z'],
        "abcdefghijklmnopqrstuvwxyz".chars().collect(),
        vec!['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j'],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6];

    for seed_chars in &curated_seeds {
        for &mk in &mutation_kinds {
            let (s, t) = mutate(seed_chars.clone(), mk);
            emit(&s, &t, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations across size classes
    while count < target_count {
        let n: usize = match count % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 5000),
        };
        let chars = random_lowercase_chars(&mut rng, n);
        let mk = rng.gen_range_usize(0, 6) as u8;
        let (s, t) = mutate(chars, mk);
        emit(&s, &t, &mut seen, &mut out, &mut count);
    }
}
