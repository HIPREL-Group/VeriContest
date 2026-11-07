use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    banned: Vec<i32>,
    n: i32,
    max_sum: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32, i32))
    requires
        1 <= banned.len() <= 10_000,
        1 <= n <= 10_000,
        1 <= max_sum <= 1_000_000_000,
        forall|i: int| 0 <= i < banned.len() ==> 1 <= #[trigger] banned[i] <= 10_000,
    ensures
        1 <= result.0.len() <= 10_000,
        1 <= result.1 <= 10_000,
        1 <= result.2 <= 1_000_000_000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 10_000,
{
    if mutation_kind == 0 {
        // identity
        (banned, n, max_sum)
    } else if mutation_kind == 1 {
        // nudge first banned element up
        let mut b = banned;
        if b[0] < 10_000 {
            b.set(0, b[0] + 1);
        }
        (b, n, max_sum)
    } else if mutation_kind == 2 {
        // nudge first banned element down
        let mut b = banned;
        if b[0] > 1 {
            b.set(0, b[0] - 1);
        }
        (b, n, max_sum)
    } else if mutation_kind == 3 {
        // set first banned element to boundary 1
        let mut b = banned;
        b.set(0, 1);
        (b, n, max_sum)
    } else if mutation_kind == 4 {
        // set first banned element to boundary 10_000
        let mut b = banned;
        b.set(0, 10_000);
        (b, n, max_sum)
    } else if mutation_kind == 5 && banned.len() < 10_000 {
        // grow banned by pushing element 1
        let mut b = banned;
        b.push(1);
        (b, n, max_sum)
    } else if mutation_kind == 6 && banned.len() > 1 {
        // shrink banned by popping last element
        let mut b = banned;
        b.pop();
        (b, n, max_sum)
    } else if mutation_kind == 7 {
        // set all banned to same value (first element)
        let val = banned[0];
        let mut b = banned;
        let mut i: usize = 0;
        while i < b.len()
            invariant
                0 <= i <= b.len(),
                b.len() == banned.len(),
                1 <= b.len() <= 10_000,
                1 <= val <= 10_000,
                forall|j: int| 0 <= j < i ==> b[j] == val,
                forall|j: int| i <= j < b.len() ==> b[j] == banned[j],
            decreases b.len() - i,
        {
            b.set(i, val);
            i += 1;
        }
        (b, n, max_sum)
    } else if mutation_kind == 8 {
        // set n to 1
        (banned, 1, max_sum)
    } else if mutation_kind == 9 {
        // set n to 10_000
        (banned, 10_000, max_sum)
    } else if mutation_kind == 10 {
        // set max_sum to 1
        (banned, n, 1)
    } else if mutation_kind == 11 {
        // set max_sum to 1_000_000_000
        (banned, n, 1_000_000_000)
    } else if mutation_kind == 12 {
        // nudge n up
        if n < 10_000 {
            (banned, n + 1, max_sum)
        } else {
            (banned, n, max_sum)
        }
    } else if mutation_kind == 13 {
        // nudge n down
        if n > 1 {
            (banned, n - 1, max_sum)
        } else {
            (banned, n, max_sum)
        }
    } else if mutation_kind == 14 {
        // nudge max_sum up
        if max_sum < 1_000_000_000 {
            (banned, n, max_sum + 1)
        } else {
            (banned, n, max_sum)
        }
    } else if mutation_kind == 15 {
        // nudge max_sum down
        if max_sum > 1 {
            (banned, n, max_sum - 1)
        } else {
            (banned, n, max_sum)
        }
    } else {
        // fallback: identity
        (banned, n, max_sum)
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

fn mutate(banned: Vec<i32>, n: i32, max_sum: i32, mutation_kind: u8) -> (Vec<i32>, i32, i32) {
    generate_test_case(banned, n, max_sum, mutation_kind)
}

fn random_banned(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut banned = Vec::with_capacity(len);
    for _ in 0..len {
        banned.push(rng.gen_range_i64(1, 10_000) as i32);
    }
    banned
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2554);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |banned: Vec<i32>, n: i32, max_sum: i32,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= target { return; }
        let key = format!("{:?}_{}_{}",  banned, n, max_sum);
        if !seen.insert(key) { return; }
        let output = Solution::max_count(banned.clone(), n, max_sum);
        writeln!(out, "{}", json!({
            "input": {"banned": banned, "n": n, "maxSum": max_sum},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example test cases from description.md
    let examples: Vec<(Vec<i32>, i32, i32)> = vec![
        (vec![1, 6, 5], 5, 6),
        (vec![1, 2, 3, 4, 5, 6, 7], 8, 1),
        (vec![11], 7, 50),
    ];
    for (b, n, ms) in &examples {
        emit(b.clone(), *n, *ms, &mut seen, &mut out, &mut count);
    }

    // Seed test cases: interesting banned arrays × n × max_sum combos
    let seed_banned: Vec<Vec<i32>> = vec![
        vec![1],
        vec![1, 2, 3],
        vec![10_000],
        vec![5, 5, 5],
        vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
        vec![100, 200, 300],
    ];
    let seed_n_ms: Vec<(i32, i32)> = vec![
        (1, 1),
        (10, 100),
        (100, 5000),
        (10_000, 1_000_000_000),
        (5, 3),
        (1000, 500_000),
    ];
    let mutation_kinds: Vec<u8> = (0..=15).collect();

    for b in &seed_banned {
        for &(n, ms) in &seed_n_ms {
            for &mk in &mutation_kinds {
                let (rb, rn, rms) = mutate(b.clone(), n, ms, mk);
                emit(rb, rn, rms, &mut seen, &mut out, &mut count);
            }
        }
    }

    // Random test cases with random mutations
    while count < target {
        let blen = match count % 5 {
            0 => rng.gen_range_usize(1, 3),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 100),    // medium
            3 => rng.gen_range_usize(101, 1000),  // large
            _ => rng.gen_range_usize(1001, 10_000), // max
        };
        let b = random_banned(&mut rng, blen);
        let n = rng.gen_range_i64(1, 10_000) as i32;
        let ms = rng.gen_range_i64(1, 1_000_000_000) as i32;
        let mk = rng.gen_range_usize(0, 15) as u8;
        let (rb, rn, rms) = mutate(b, n, ms, mk);
        emit(rb, rn, rms, &mut seen, &mut out, &mut count);
    }
}
