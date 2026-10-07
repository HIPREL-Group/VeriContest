use vstd::prelude::*;
use vstd::string::*;

verus! {

pub fn generate_test_case(colors: String, mutation_kind: u8) -> (result: String)
    requires
        1 <= colors@.len() <= 100_000,
        forall |i: int| 0 <= i < colors@.len() ==> colors@[i] == 'A' || colors@[i] == 'B',
    ensures
        1 <= result@.len() <= 100_000,
        forall |i: int| 0 <= i < result@.len() ==> result@[i] == 'A' || result@[i] == 'B',
{
    if mutation_kind == 0 {
        // identity
        colors
    } else {
        // fallback: identity
        colors
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

fn random_ab_string(rng: &mut Rng, len: usize) -> String {
    let mut s = String::new();
    for _ in 0..len {
        if rng.gen_range_usize(0, 1) == 0 {
            s.push('A');
        } else {
            s.push('B');
        }
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

    let mut emit = |colors: String,
                    out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count { return; }
        let output = Solution::winner_of_game(colors.clone());
        writeln!(out, "{}", json!({
            "input": {"colors": colors},
            "output": output
        })).unwrap();
        *emitted += 1;
    };

    // Example inputs from description.md
    emit("AAABABB".to_string(), &mut out, &mut emitted);
    emit("AA".to_string(), &mut out, &mut emitted);
    emit("ABBBBBBBAAA".to_string(), &mut out, &mut emitted);

    // Edge cases
    emit("A".to_string(), &mut out, &mut emitted);
    emit("B".to_string(), &mut out, &mut emitted);
    emit("AB".to_string(), &mut out, &mut emitted);
    emit("BA".to_string(), &mut out, &mut emitted);
    emit("AAA".to_string(), &mut out, &mut emitted);
    emit("BBB".to_string(), &mut out, &mut emitted);
    emit("AAABBB".to_string(), &mut out, &mut emitted);
    emit("BBBAA".to_string(), &mut out, &mut emitted);
    emit("AAAAAA".to_string(), &mut out, &mut emitted);
    emit("BBBBBB".to_string(), &mut out, &mut emitted);
    emit("ABABABABAB".to_string(), &mut out, &mut emitted);
    emit("AAAAAABBBBBB".to_string(), &mut out, &mut emitted);
    emit("BBBBBBAAAAAAA".to_string(), &mut out, &mut emitted);
    emit("AAABBBAAABBB".to_string(), &mut out, &mut emitted);

    // Boundary: all A's and all B's at various lengths
    for &len in &[1, 2, 3, 5, 10, 100, 1000] {
        if emitted >= count { break; }
        emit("A".repeat(len), &mut out, &mut emitted);
        if emitted >= count { break; }
        emit("B".repeat(len), &mut out, &mut emitted);
    }

    // Random test cases with diverse sizes
    while emitted < count {
        let len = match emitted % 5 {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 100),      // medium
            3 => rng.gen_range_usize(101, 1000),    // large
            _ => rng.gen_range_usize(1001, 10000),  // very large
        };
        let colors = random_ab_string(&mut rng, len);
        let mk = rng.gen_range_usize(0, 1) as u8;
        let result = generate_test_case(colors, mk);
        emit(result, &mut out, &mut emitted);
    }
}
