use vstd::prelude::*;

verus! {

pub fn generate_test_case(chars: Vec<char>, mutation_kind: u8) -> (result: Vec<char>)
    requires
        1 <= chars.len() <= 100000,
        forall|i: int| 0 <= i < chars.len() ==> (#[trigger] chars[i] >= 'a' && chars[i] <= 'z'),
    ensures
        1 <= result.len() <= 100000,
{
    if mutation_kind == 0 {
        // identity
        chars
    } else if mutation_kind == 1 && chars.len() >= 2 {
        // mirror first half onto second half (palindrome)
        let mut s = chars;
        let n = s.len();
        let mut i: usize = 0;
        while i < n / 2
            invariant
                0 <= i <= n / 2,
                s.len() == n,
                n == chars.len(),
                1 <= n <= 100000,
            decreases n / 2 - i,
        {
            let mirror = n - 1 - i;
            s.set(mirror, s[i]);
            i += 1;
        }
        s
    } else if mutation_kind == 2 && chars.len() >= 3 {
        // near-palindrome: mirror then tweak middle
        let mut s = chars;
        let n = s.len();
        let mut i: usize = 0;
        while i < n / 2
            invariant
                0 <= i <= n / 2,
                s.len() == n,
                n == chars.len(),
                1 <= n <= 100000,
            decreases n / 2 - i,
        {
            let mirror = n - 1 - i;
            s.set(mirror, s[i]);
            i += 1;
        }
        let mid = n / 2;
        let c = s[mid];
        if c == 'a' {
            s.set(mid, 'b');
        } else {
            s.set(mid, 'a');
        }
        s
    } else if mutation_kind == 3 && chars.len() < 100000 {
        // grow by one
        let mut s = chars;
        s.push('a');
        s
    } else if mutation_kind == 4 && chars.len() > 1 {
        // shrink by one
        let mut s = chars;
        s.pop();
        s
    } else if mutation_kind == 5 {
        // set all chars to 'a' (palindrome)
        let mut s = chars;
        let n = s.len();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                s.len() == n,
                n == chars.len(),
                1 <= n <= 100000,
            decreases n - i,
        {
            s.set(i, 'a');
            i += 1;
        }
        s
    } else if mutation_kind == 6 && chars.len() >= 2 {
        // swap first two characters
        let mut s = chars;
        let c0 = s[0];
        let c1 = s[1];
        s.set(0, c1);
        s.set(1, c0);
        s
    } else if mutation_kind == 7 {
        // set first='z', last='a' (likely not palindrome)
        let mut s = chars;
        let last = s.len() - 1;
        s.set(0, 'z');
        s.set(last, 'a');
        s
    } else {
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

    fn gen_char(&mut self) -> char {
        (b'a' + (self.next_u64() % 26) as u8) as char
    }
}

struct Solution;
include!("../code.rs");

fn make_random_chars(rng: &mut Rng, n: usize) -> Vec<char> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_char());
    }
    v
}

fn make_palindrome(rng: &mut Rng, n: usize) -> Vec<char> {
    let mut v = make_random_chars(rng, n);
    for i in 0..n / 2 {
        v[n - 1 - i] = v[i];
    }
    v
}

fn chars_to_string(chars: &[char]) -> String {
    chars.iter().collect()
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    use std::io::Write;

    // Example inputs from description.md
    let examples: Vec<Vec<char>> = vec![
        "aba".chars().collect(),
        "abca".chars().collect(),
        "abc".chars().collect(),
    ];
    for ex in &examples {
        let s_clone = ex.clone();
        let result = Solution::valid_palindrome(s_clone);
        let s_str: String = chars_to_string(ex);
        writeln!(out, "{}", json!({
            "input": {"s": s_str},
            "output": result
        })).unwrap();
    }

    let num_mutations: u8 = 8;
    let mut generated = examples.len();

    while generated < count {
        let n: usize = match generated % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 10000),
        };

        let base_chars = match generated % 4 {
            0 => make_random_chars(&mut rng, n),
            1 => make_palindrome(&mut rng, n),
            2 => {
                let mut p = make_palindrome(&mut rng, n);
                if n >= 2 {
                    let pos = rng.gen_range_usize(0, n - 1);
                    p[pos] = rng.gen_char();
                }
                p
            }
            _ => vec!['a'; n],
        };

        let mutation = (rng.next_u64() % num_mutations as u64) as u8;
        let result_chars = generate_test_case(base_chars.clone(), mutation);
        let s_clone = result_chars.clone();
        let output = Solution::valid_palindrome(s_clone);
        let s_str: String = chars_to_string(&result_chars);

        writeln!(out, "{}", json!({
            "input": {"s": s_str},
            "output": output
        })).unwrap();

        generated += 1;
    }

    eprintln!("Generated {} test cases to {:?}", generated, out_path);
}
