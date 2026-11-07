use vstd::prelude::*;
use vstd::string::*;

verus! {

pub fn generate_test_case(s: String, mutation_kind: u8) -> (result: String)
    requires
        1 <= s@.len() <= 1_000,
        forall|i: int| 0 <= i < s@.len() ==> s@[i] == 'A' || s@[i] == 'L' || s@[i] == 'P',
    ensures
        1 <= result@.len() <= 1_000,
        forall|i: int| 0 <= i < result@.len() ==> result@[i] == 'A' || result@[i] == 'L' || result@[i] == 'P',
{
    let len = s.as_str().unicode_len();

    if mutation_kind == 0 {
        // identity
        s
    } else if mutation_kind == 1 && len > 1 {
        // remove last character
        let sub = s.as_str().substring_char(0, len - 1);
        let r = String::from_str(sub);
        proof {
            assert forall|i: int| 0 <= i < r@.len() implies
                r@[i] == 'A' || r@[i] == 'L' || r@[i] == 'P' by {
                assert(s@.subrange(0int, (len - 1) as int)[i] == s@[i]);
            }
        }
        r
    } else if mutation_kind == 2 && len > 1 {
        // remove first character
        let sub = s.as_str().substring_char(1, len);
        let r = String::from_str(sub);
        proof {
            assert forall|i: int| 0 <= i < r@.len() implies
                r@[i] == 'A' || r@[i] == 'L' || r@[i] == 'P' by {
                assert(s@.subrange(1int, len as int)[i] == s@[i + 1]);
            }
        }
        r
    } else if mutation_kind == 3 && len > 2 {
        // take first half
        let half = len / 2;
        let sub = s.as_str().substring_char(0, half);
        let r = String::from_str(sub);
        proof {
            assert forall|i: int| 0 <= i < r@.len() implies
                r@[i] == 'A' || r@[i] == 'L' || r@[i] == 'P' by {
                assert(s@.subrange(0int, half as int)[i] == s@[i]);
            }
        }
        r
    } else if mutation_kind == 4 && len > 2 {
        // take second half
        let half = len / 2;
        let sub = s.as_str().substring_char(half, len);
        let r = String::from_str(sub);
        proof {
            assert forall|i: int| 0 <= i < r@.len() implies
                r@[i] == 'A' || r@[i] == 'L' || r@[i] == 'P' by {
                assert(s@.subrange(half as int, len as int)[i] == s@[half as int + i]);
            }
        }
        r
    } else if mutation_kind == 5 && len <= 500 {
        // double the string
        let c = s.clone();
        let mut r = c;
        r.append(s.as_str());
        proof {
            assert forall|i: int| 0 <= i < r@.len() implies
                r@[i] == 'A' || r@[i] == 'L' || r@[i] == 'P' by {
                if i < s@.len() as int {
                    assert(r@[i] == s@[i]);
                } else {
                    assert(r@[i] == s@[i - s@.len()]);
                }
            }
        }
        r
    } else if mutation_kind == 6 {
        // take just the first character
        let sub = s.as_str().substring_char(0, 1);
        let r = String::from_str(sub);
        proof {
            assert forall|i: int| 0 <= i < r@.len() implies
                r@[i] == 'A' || r@[i] == 'L' || r@[i] == 'P' by {
                assert(s@.subrange(0int, 1int)[i] == s@[i]);
            }
        }
        r
    } else if mutation_kind == 7 {
        // take just the last character
        let sub = s.as_str().substring_char(len - 1, len);
        let r = String::from_str(sub);
        proof {
            assert forall|i: int| 0 <= i < r@.len() implies
                r@[i] == 'A' || r@[i] == 'L' || r@[i] == 'P' by {
                assert(s@.subrange((len - 1) as int, len as int)[i]
                    == s@[(len - 1) as int + i]);
            }
        }
        r
    } else {
        // fallback: identity
        s
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

fn random_alp_string(rng: &mut Rng, len: usize) -> String {
    let mut s = String::with_capacity(len);
    for _ in 0..len {
        let c = match rng.gen_range_usize(0, 2) {
            0 => 'A',
            1 => 'L',
            _ => 'P',
        };
        s.push(c);
    }
    s
}

fn mutate(s: String, mutation_kind: u8) -> String {
    generate_test_case(s, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |s: String, seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= goal || !seen.insert(s.clone()) { return; }
        let output = Solution::check_record(s.clone());
        writeln!(out, "{}", json!({"input": {"s": s}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    emit("PPALLP".to_string(), &mut seen, &mut out, &mut count);
    emit("PPALLL".to_string(), &mut seen, &mut out, &mut count);

    // Interesting hand-crafted seeds with all mutation kinds
    let seeds: Vec<String> = vec![
        "P".to_string(),
        "A".to_string(),
        "L".to_string(),
        "AA".to_string(),
        "LLL".to_string(),
        "LL".to_string(),
        "ALLL".to_string(),
        "PPPPP".to_string(),
        "APA".to_string(),
        "PLLPLLP".to_string(),
        "LLALLALL".to_string(),
        "PPPPPPPPPP".to_string(),
        "LLLLLLLLLLL".to_string(),
        "AAAAAAAAAA".to_string(),
        "PALLPALLP".to_string(),
    ];

    for seed_str in &seeds {
        for mk in 0..=7u8 {
            let result = mutate(seed_str.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds across size classes with random mutations
    for i in 0..goal * 3 {
        if count >= goal { break; }
        let len = match i % 5 {
            0 => rng.gen_range_usize(1, 5),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 100),    // medium
            3 => rng.gen_range_usize(101, 500),   // large
            _ => rng.gen_range_usize(501, 1000),  // max
        };
        let s = random_alp_string(&mut rng, len);
        let mk = rng.gen_range_usize(0, 7) as u8;
        let result = mutate(s, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
