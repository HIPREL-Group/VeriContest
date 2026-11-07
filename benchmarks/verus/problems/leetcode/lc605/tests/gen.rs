use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    raw: Vec<i32>,
    n_val: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= raw.len() <= 20_000,
        forall|i: int| 0 <= i < raw.len() ==> (#[trigger] raw[i] == 0 || raw[i] == 1),
        0 <= n_val <= raw.len(),
    ensures
        1 <= result.0.len() <= 20_000,
        forall|i: int| 0 <= i < result.0.len() ==> (#[trigger] result.0[i] == 0 || result.0[i] == 1),
        forall|i: int| 0 <= i < result.0.len() - 1 ==> !(#[trigger] result.0[i] == 1 && result.0[i + 1] == 1),
        0 <= result.1 <= result.0.len(),
{
    // Build a valid flowerbed by suppressing adjacent 1s from raw input
    let mut fb: Vec<i32> = Vec::new();
    let mut prev_one: bool = false;
    let mut k: usize = 0;
    while k < raw.len()
        invariant
            k <= raw.len(),
            fb.len() == k,
            1 <= raw.len() <= 20_000,
            forall|i: int| 0 <= i < raw.len() ==> (#[trigger] raw[i] == 0 || raw[i] == 1),
            forall|i: int| 0 <= i < fb.len() ==> (#[trigger] fb[i] == 0 || fb[i] == 1),
            forall|i: int| 0 <= i < fb.len() - 1 ==> !(#[trigger] fb[i] == 1 && fb[i + 1] == 1),
            prev_one == (k > 0 && fb[k as int - 1] == 1),
        decreases raw.len() - k,
    {
        if raw[k] == 1 && !prev_one {
            fb.push(1);
            prev_one = true;
        } else {
            fb.push(0);
            prev_one = false;
        }
        k += 1;
    }

    // After the loop: fb.len() == raw.len(), so n_val is valid
    assert(fb.len() == raw.len());

    if mutation_kind == 0 {
        // identity
        (fb, n_val)
    } else if mutation_kind == 1 {
        // set first element to 0 (remove flower at start)
        let mut d = fb;
        d.set(0, 0);
        (d, n_val)
    } else if mutation_kind == 2 {
        // set last element to 0 (remove flower at end)
        let mut d = fb;
        let last = d.len() - 1;
        d.set(last, 0);
        (d, n_val)
    } else if mutation_kind == 3 && fb.len() < 20_000 {
        // grow by appending 0
        let mut d = fb;
        d.push(0);
        (d, n_val)
    } else if mutation_kind == 4 && fb.len() > 1 {
        // shrink by popping last element
        let mut d = fb;
        d.pop();
        let n2 = if n_val > d.len() as i32 { d.len() as i32 } else { n_val };
        (d, n2)
    } else if mutation_kind == 5 {
        // set n to 0
        (fb, 0i32)
    } else if mutation_kind == 6 {
        // set n to length (maximum)
        let n2 = fb.len() as i32;
        (fb, n2)
    } else {
        // fallback: identity
        (fb, n_val)
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

fn gen(raw: Vec<i32>, n_val: i32, mutation_kind: u8) -> (Vec<i32>, i32) {
    generate_test_case(raw, n_val, mutation_kind)
}

fn random_flowerbed_raw(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut raw = Vec::with_capacity(len);
    for _ in 0..len {
        raw.push(rng.gen_range_i64(0, 1) as i32);
    }
    raw
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(605);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |flowerbed: Vec<i32>, n: i32,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}_{}", flowerbed, n);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::can_place_flowers(flowerbed.clone(), n);
        writeln!(out, "{}", json!({
            "input": {"flowerbed": flowerbed, "n": n},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example test cases from description.md
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![1, 0, 0, 0, 1], 1),
        (vec![1, 0, 0, 0, 1], 2),
    ];
    for (fb, n) in examples {
        emit(fb, n, &mut seen, &mut out, &mut count);
    }

    // Seed flowerbeds with interesting patterns
    let seed_beds: Vec<Vec<i32>> = vec![
        vec![0],
        vec![1],
        vec![0, 0],
        vec![1, 0],
        vec![0, 1],
        vec![0, 0, 0],
        vec![1, 0, 0],
        vec![0, 0, 1],
        vec![1, 0, 1],
        vec![0, 0, 0, 0, 0],
        vec![1, 0, 1, 0, 1],
        vec![0, 1, 0, 1, 0],
        vec![1, 0, 0, 0, 0, 0, 1],
        vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];

    // Apply every mutation to every seed
    for bed in &seed_beds {
        for &mk in &mutation_kinds {
            let n = rng.gen_range_i64(0, bed.len() as i64) as i32;
            let (fb, nv) = gen(bed.clone(), n, mk);
            emit(fb, nv, &mut seen, &mut out, &mut count);
        }
    }

    // Random flowerbeds across diverse size classes
    while count < target {
        let len: usize = match count % 5 {
            0 => rng.gen_range_usize(1, 5),       // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 1000),   // large
            _ => rng.gen_range_usize(1001, 20_000), // max
        };
        let raw = random_flowerbed_raw(&mut rng, len);
        let n = rng.gen_range_i64(0, len as i64) as i32;
        let mk = rng.gen_range_usize(0, 7) as u8;
        let (fb, nv) = gen(raw, n, mk);
        emit(fb, nv, &mut seen, &mut out, &mut count);
    }
}
