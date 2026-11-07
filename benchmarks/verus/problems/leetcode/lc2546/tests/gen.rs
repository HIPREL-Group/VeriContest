use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    s_char: u8,
    t_char: u8,
    mutation_kind: u8,
) -> (result: (Vec<char>, Vec<char>))
    requires
        2 <= n <= 100000,
        s_char == 0 || s_char == 1,
        t_char == 0 || t_char == 1,
    ensures
        2 <= result.0@.len() == result.1@.len() <= 100000,
        forall |i: int| 0 <= i < result.0@.len() ==> result.0@[i] == '0' || result.0@[i] == '1',
        forall |i: int| 0 <= i < result.1@.len() ==> result.1@[i] == '0' || result.1@[i] == '1',
{
    let s_fill: char = if s_char == 0 { '0' } else { '1' };
    let t_fill: char = if t_char == 0 { '0' } else { '1' };

    let mut s: Vec<char> = Vec::new();
    let mut target: Vec<char> = Vec::new();

    if mutation_kind == 0 {
        // Both filled uniformly with chosen chars
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                2 <= n <= 100000,
                s@.len() == i,
                target@.len() == i,
                s_fill == '0' || s_fill == '1',
                t_fill == '0' || t_fill == '1',
                forall |k: int| 0 <= k < s@.len() ==> s@[k] == '0' || s@[k] == '1',
                forall |k: int| 0 <= k < target@.len() ==> target@[k] == '0' || target@[k] == '1',
            decreases n - i,
        {
            s.push(s_fill);
            target.push(t_fill);
            i = i + 1;
        }
    } else if mutation_kind == 1 {
        // s: '1' only at first position, rest '0'; target: uniform fill
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                2 <= n <= 100000,
                s@.len() == i,
                target@.len() == i,
                t_fill == '0' || t_fill == '1',
                forall |k: int| 0 <= k < s@.len() ==> s@[k] == '0' || s@[k] == '1',
                forall |k: int| 0 <= k < target@.len() ==> target@[k] == '0' || target@[k] == '1',
            decreases n - i,
        {
            if i == 0 {
                s.push('1');
            } else {
                s.push('0');
            }
            target.push(t_fill);
            i = i + 1;
        }
    } else if mutation_kind == 2 {
        // s: uniform fill; target: '1' only at last position, rest '0'
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                2 <= n <= 100000,
                s@.len() == i,
                target@.len() == i,
                s_fill == '0' || s_fill == '1',
                forall |k: int| 0 <= k < s@.len() ==> s@[k] == '0' || s@[k] == '1',
                forall |k: int| 0 <= k < target@.len() ==> target@[k] == '0' || target@[k] == '1',
            decreases n - i,
        {
            s.push(s_fill);
            if i == n - 1 {
                target.push('1');
            } else {
                target.push('0');
            }
            i = i + 1;
        }
    } else if mutation_kind == 3 {
        // Alternating pattern for s; opposite alternating for target
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                2 <= n <= 100000,
                s@.len() == i,
                target@.len() == i,
                forall |k: int| 0 <= k < s@.len() ==> s@[k] == '0' || s@[k] == '1',
                forall |k: int| 0 <= k < target@.len() ==> target@[k] == '0' || target@[k] == '1',
            decreases n - i,
        {
            if i % 2 == 0 {
                s.push('0');
                target.push('1');
            } else {
                s.push('1');
                target.push('0');
            }
            i = i + 1;
        }
    } else if mutation_kind == 4 {
        // Both all zeros
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                2 <= n <= 100000,
                s@.len() == i,
                target@.len() == i,
                forall |k: int| 0 <= k < s@.len() ==> s@[k] == '0' || s@[k] == '1',
                forall |k: int| 0 <= k < target@.len() ==> target@[k] == '0' || target@[k] == '1',
            decreases n - i,
        {
            s.push('0');
            target.push('0');
            i = i + 1;
        }
    } else if mutation_kind == 5 {
        // Both all ones
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                2 <= n <= 100000,
                s@.len() == i,
                target@.len() == i,
                forall |k: int| 0 <= k < s@.len() ==> s@[k] == '0' || s@[k] == '1',
                forall |k: int| 0 <= k < target@.len() ==> target@[k] == '0' || target@[k] == '1',
            decreases n - i,
        {
            s.push('1');
            target.push('1');
            i = i + 1;
        }
    } else if mutation_kind == 6 {
        // s all ones, target all zeros (answer = false)
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                2 <= n <= 100000,
                s@.len() == i,
                target@.len() == i,
                forall |k: int| 0 <= k < s@.len() ==> s@[k] == '0' || s@[k] == '1',
                forall |k: int| 0 <= k < target@.len() ==> target@[k] == '0' || target@[k] == '1',
            decreases n - i,
        {
            s.push('1');
            target.push('0');
            i = i + 1;
        }
    } else if mutation_kind == 7 {
        // s all zeros, target all ones (answer = false)
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                2 <= n <= 100000,
                s@.len() == i,
                target@.len() == i,
                forall |k: int| 0 <= k < s@.len() ==> s@[k] == '0' || s@[k] == '1',
                forall |k: int| 0 <= k < target@.len() ==> target@[k] == '0' || target@[k] == '1',
            decreases n - i,
        {
            s.push('0');
            target.push('1');
            i = i + 1;
        }
    } else {
        // Fallback: uniform fill
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                2 <= n <= 100000,
                s@.len() == i,
                target@.len() == i,
                s_fill == '0' || s_fill == '1',
                t_fill == '0' || t_fill == '1',
                forall |k: int| 0 <= k < s@.len() ==> s@[k] == '0' || s@[k] == '1',
                forall |k: int| 0 <= k < target@.len() ==> target@[k] == '0' || target@[k] == '1',
            decreases n - i,
        {
            s.push(s_fill);
            target.push(t_fill);
            i = i + 1;
        }
    }

    (s, target)
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

    fn gen_bool(&mut self) -> bool {
        self.next_u64() % 2 == 0
    }
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

    // Helper: convert Vec<char> to String and compute output
    let mut emit = |s_chars: Vec<char>, t_chars: Vec<char>, out: &mut std::io::BufWriter<std::fs::File>| {
        let s_str: String = s_chars.iter().collect();
        let t_str: String = t_chars.iter().collect();
        let output = Solution::make_strings_equal(s_str.clone(), t_str.clone());
        writeln!(out, "{}", json!({
            "input": {"s": s_str, "target": t_str},
            "output": output
        })).unwrap();
    };

    // Example inputs from description.md
    {
        let s: Vec<char> = "1010".chars().collect();
        let t: Vec<char> = "0110".chars().collect();
        emit(s, t, &mut out);
        emitted += 1;
    }
    {
        let s: Vec<char> = "11".chars().collect();
        let t: Vec<char> = "00".chars().collect();
        emit(s, t, &mut out);
        emitted += 1;
    }

    // Systematic: all mutation_kinds × a few sizes
    let sizes: [usize; 5] = [2, 5, 50, 500, 100000];
    for &n in &sizes {
        for mk in 0..=8u8 {
            if emitted >= count { break; }
            let sc = if mk % 3 == 0 { 0u8 } else { 1u8 };
            let tc = if mk % 2 == 0 { 0u8 } else { 1u8 };
            let (s_chars, t_chars) = generate_test_case(n, sc, tc, mk);
            emit(s_chars, t_chars, &mut out);
            emitted += 1;
        }
    }

    // Random test cases to fill remaining
    while emitted < count {
        let n = match emitted % 5 {
            0 => rng.gen_range_usize(2, 5),
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 100000),
        };
        let sc = if rng.gen_bool() { 1u8 } else { 0u8 };
        let tc = if rng.gen_bool() { 1u8 } else { 0u8 };
        let mk = rng.gen_u8() % 9;
        let (s_chars, t_chars) = generate_test_case(n, sc, tc, mk);
        emit(s_chars, t_chars, &mut out);
        emitted += 1;
    }
}
