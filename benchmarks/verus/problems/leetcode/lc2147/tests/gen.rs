use vstd::prelude::*;
use vstd::string::*;

verus! {

pub fn generate_test_case(corridor: String, mutation_kind: u8) -> (result: String)
    requires
        1 <= corridor@.len() <= 100_000,
        forall|i: int| 0 <= i < corridor@.len() ==> corridor@[i] == 'S' || corridor@[i] == 'P',
    ensures
        1 <= result@.len() <= 100_000,
        forall|i: int| 0 <= i < result@.len() ==> result@[i] == 'S' || result@[i] == 'P',
{
    let len = corridor.as_str().unicode_len();

    if mutation_kind == 0 {
        // identity
        corridor
    } else if mutation_kind == 1 && len > 1 {
        // remove last character
        let sub = corridor.as_str().substring_char(0, len - 1);
        let r = String::from_str(sub);
        proof {
            assert forall|i: int| 0 <= i < r@.len() implies r@[i] == 'S' || r@[i] == 'P' by {
                assert(corridor@.subrange(0int, (len - 1) as int)[i] == corridor@[i]);
            }
        }
        r
    } else if mutation_kind == 2 && len > 1 {
        // remove first character
        let sub = corridor.as_str().substring_char(1, len);
        let r = String::from_str(sub);
        proof {
            assert forall|i: int| 0 <= i < r@.len() implies r@[i] == 'S' || r@[i] == 'P' by {
                assert(corridor@.subrange(1int, len as int)[i] == corridor@[i + 1]);
            }
        }
        r
    } else if mutation_kind == 3 && len > 2 {
        // take first half
        let half = len / 2;
        let sub = corridor.as_str().substring_char(0, half);
        let r = String::from_str(sub);
        proof {
            assert forall|i: int| 0 <= i < r@.len() implies r@[i] == 'S' || r@[i] == 'P' by {
                assert(corridor@.subrange(0int, half as int)[i] == corridor@[i]);
            }
        }
        r
    } else if mutation_kind == 4 && len > 2 {
        // take second half
        let half = len / 2;
        let sub = corridor.as_str().substring_char(half, len);
        let r = String::from_str(sub);
        proof {
            assert forall|i: int| 0 <= i < r@.len() implies r@[i] == 'S' || r@[i] == 'P' by {
                assert(corridor@.subrange(half as int, len as int)[i] == corridor@[half as int + i]);
            }
        }
        r
    } else if mutation_kind == 5 && len <= 50_000 {
        // double the string
        let c = corridor.clone();
        let mut r = c;
        r.append(corridor.as_str());
        proof {
            assert forall|i: int| 0 <= i < r@.len() implies r@[i] == 'S' || r@[i] == 'P' by {
                if i < corridor@.len() as int {
                    assert(r@[i] == corridor@[i]);
                } else {
                    assert(r@[i] == corridor@[i - corridor@.len()]);
                }
            }
        }
        r
    } else if mutation_kind == 6 {
        // take just the first character
        let sub = corridor.as_str().substring_char(0, 1);
        let r = String::from_str(sub);
        proof {
            assert forall|i: int| 0 <= i < r@.len() implies r@[i] == 'S' || r@[i] == 'P' by {
                assert(corridor@.subrange(0int, 1int)[i] == corridor@[i]);
            }
        }
        r
    } else if mutation_kind == 7 {
        // take just the last character
        let sub = corridor.as_str().substring_char(len - 1, len);
        let r = String::from_str(sub);
        proof {
            assert forall|i: int| 0 <= i < r@.len() implies r@[i] == 'S' || r@[i] == 'P' by {
                assert(corridor@.subrange((len - 1) as int, len as int)[i]
                    == corridor@[(len - 1) as int + i]);
            }
        }
        r
    } else {
        // fallback: identity
        corridor
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
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

fn make_corridor(rng: &mut Rng, len: usize) -> String {
    let mut s = std::string::String::with_capacity(len);
    for _ in 0..len {
        if rng.gen_range_usize(0, 1) == 0 {
            s.push('S');
        } else {
            s.push('P');
        }
    }
    s
}

fn make_corridor_pattern(pattern: &str, len: usize) -> String {
    let chars: Vec<char> = pattern.chars().collect();
    let mut s = std::string::String::with_capacity(len);
    for i in 0..len {
        s.push(chars[i % chars.len()]);
    }
    s
}

fn number_of_ways_exec(corridor: &str) -> i32 {
    let mod_num: u128 = 1_000_000_007;
    let mut seat_count: usize = 0;
    let mut plants: usize = 0;
    let mut ways: u128 = 1;

    for c in corridor.chars() {
        if c == 'S' {
            if seat_count >= 2 && seat_count % 2 == 0 {
                ways = (ways * (plants as u128 + 1)) % mod_num;
            }
            seat_count += 1;
            plants = 0;
        } else {
            if seat_count >= 2 && seat_count % 2 == 0 {
                plants += 1;
            }
        }
    }

    if seat_count == 0 || seat_count % 2 == 1 {
        0
    } else {
        ways as i32
    }
}

fn mutate(corridor: String, mutation_kind: u8) -> String {
    generate_test_case(corridor, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2147);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |corridor: String, seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count || !seen.insert(corridor.clone()) {
            return;
        }
        let output = number_of_ways_exec(&corridor);
        writeln!(out, "{}", json!({
            "input": {"corridor": corridor},
            "output": output
        })).unwrap();
        *emitted += 1;
    };

    // Example inputs from the problem description
    let examples: Vec<String> = vec![
        "SSPPSPS".to_string(),
        "PPSPSP".to_string(),
        "S".to_string(),
    ];
    for ex in examples {
        emit(ex, &mut seen, &mut out, &mut emitted);
    }

    // Diverse seed strings covering structural patterns
    let seeds: Vec<String> = vec![
        "S".to_string(),
        "P".to_string(),
        "SS".to_string(),
        "PP".to_string(),
        "SP".to_string(),
        "PS".to_string(),
        "SSS".to_string(),
        "SSSS".to_string(),
        "PPPP".to_string(),
        "SPSP".to_string(),
        "SSPPSS".to_string(),
        "SSPSS".to_string(),
        "SSPPPPSS".to_string(),
        "SSPPSSP".to_string(),
        make_corridor_pattern("S", 10),             // all seats
        make_corridor_pattern("P", 10),             // all plants
        make_corridor_pattern("SP", 10),            // alternating
        make_corridor_pattern("SSPP", 12),          // pairs with plants
        make_corridor_pattern("SS", 20),            // consecutive seat pairs
        make_corridor_pattern("SSPPPPP", 21),       // sparse seats
        make_corridor_pattern("S", 100),            // large all seats
        make_corridor_pattern("SSPP", 100),         // large pairs
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut emitted);
        }
    }

    // Random corridors with size classes
    let mut _attempts_0 = 0usize;
    while emitted < count {
        _attempts_0 += 1; if _attempts_0 > 10000 { break; }
        let n: usize = match emitted % 5 {
            0 => rng.gen_range_usize(1, 5),         // tiny
            1 => rng.gen_range_usize(1, 10),        // small
            2 => rng.gen_range_usize(11, 100),      // medium
            3 => rng.gen_range_usize(101, 1000),    // large
            _ => rng.gen_range_usize(1001, 10000),  // max
        };
        let corridor = make_corridor(&mut rng, n);
        let mk = rng.gen_range_usize(0, 7) as u8;
        let result = mutate(corridor, mk);
        emit(result, &mut seen, &mut out, &mut emitted);
    }
}
