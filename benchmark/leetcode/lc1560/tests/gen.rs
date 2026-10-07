use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: i32,
    rounds: Vec<i32>,
    mutation_kind: u8,
) -> (res: (i32, Vec<i32>))
    requires
        2 <= n <= 100,
        rounds.len() >= 2,
        rounds.len() <= 101,
        forall |i: int| 0 <= i < rounds.len() ==> 1 <= #[trigger] rounds[i] <= n,
        forall |i: int| 0 <= i < rounds.len() - 1 ==> (#[trigger] rounds[i]) != rounds[i + 1],
    ensures
        2 <= res.0 <= 100,
        res.1.len() >= 2,
        res.1.len() <= 101,
        forall |i: int| 0 <= i < res.1.len() ==> 1 <= #[trigger] res.1[i] <= res.0,
        forall |i: int| 0 <= i < res.1.len() - 1 ==> (#[trigger] res.1[i]) != res.1[i + 1],
{
    if mutation_kind == 0 {
        // identity
        (n, rounds)
    } else if mutation_kind == 1 && rounds[rounds.len() - 2] != 1 {
        // set last element to 1 (tests start > end wrap-around)
        let mut r = rounds;
        let last = r.len() - 1;
        r.set(last, 1);
        assert(r[last as int] == 1);
        assert(forall |i: int| 0 <= i < r.len() && i != last as int
            ==> r[i] == rounds[i]);
        (n, r)
    } else if mutation_kind == 2 && rounds[rounds.len() - 2] != n {
        // set last element to n
        let mut r = rounds;
        let last = r.len() - 1;
        r.set(last, n);
        assert(r[last as int] == n);
        assert(forall |i: int| 0 <= i < r.len() && i != last as int
            ==> r[i] == rounds[i]);
        (n, r)
    } else if mutation_kind == 3 && rounds.len() < 101 {
        // grow: append element different from last
        let mut r = rounds;
        let last_val = r[r.len() - 1];
        let new_val: i32 = if last_val < n { last_val + 1 } else { 1 };
        proof {
            assert(1 <= new_val <= n);
            assert(new_val != last_val);
        }
        let ghost old_len = r.len();
        r.push(new_val);
        assert(forall |i: int| 0 <= i < old_len ==> r[i] == rounds[i]);
        assert(r[old_len as int] == new_val);
        (n, r)
    } else if mutation_kind == 4 && rounds.len() > 2 {
        // shrink: remove last element
        let mut r = rounds;
        r.pop();
        assert(forall |i: int| 0 <= i < r.len() ==> r[i] == rounds[i]);
        (n, r)
    } else if mutation_kind == 5 && rounds[1] != 1 {
        // set first element to 1
        let mut r = rounds;
        r.set(0, 1);
        assert(r[0int] == 1);
        assert(forall |i: int| 0 <= i < r.len() && i != 0
            ==> r[i] == rounds[i]);
        (n, r)
    } else if mutation_kind == 6 && rounds[1] != n {
        // set first element to n
        let mut r = rounds;
        r.set(0, n);
        assert(r[0int] == n);
        assert(forall |i: int| 0 <= i < r.len() && i != 0
            ==> r[i] == rounds[i]);
        (n, r)
    } else if mutation_kind == 7 && n < 100 {
        // increase n by 1 (all elements still in [1, n+1])
        assert(forall |i: int| 0 <= i < rounds.len()
            ==> 1 <= #[trigger] rounds[i] <= n + 1);
        (n + 1, rounds)
    } else {
        // fallback: identity
        (n, rounds)
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

fn mutate(n: i32, rounds: Vec<i32>, mk: u8) -> (i32, Vec<i32>) {
    generate_test_case(n, rounds, mk)
}

fn random_rounds(rng: &mut Rng, n: i32, len: usize) -> Vec<i32> {
    let mut rounds = Vec::with_capacity(len);
    let first = rng.gen_range_i64(1, n as i64) as i32;
    rounds.push(first);
    for _ in 1..len {
        let prev = *rounds.last().unwrap();
        let mut next = rng.gen_range_i64(1, n as i64) as i32;
        while next == prev {
            next = rng.gen_range_i64(1, n as i64) as i32;
        }
        rounds.push(next);
    }
    rounds
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1560);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |n_val: i32, rounds_val: Vec<i32>,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= target { return; }
        let key = format!("{},{:?}", n_val, rounds_val);
        if !seen.insert(key) { return; }
        let output = Solution::most_visited(n_val, rounds_val.clone());
        writeln!(out, "{}", json!({
            "input": {"n": n_val, "rounds": rounds_val},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(i32, Vec<i32>)> = vec![
        (4, vec![1, 3, 1, 2]),
        (2, vec![2, 1, 2, 1, 2, 1, 2, 1, 2]),
        (7, vec![1, 3, 5, 7]),
    ];

    // Emit examples directly
    for (n_val, rounds_val) in &examples {
        emit(*n_val, rounds_val.clone(), &mut seen, &mut out, &mut count);
    }

    // Hand-crafted seeds covering interesting cases
    let seeds: Vec<(i32, Vec<i32>)> = vec![
        (2, vec![1, 2]),                    // minimum n, minimum rounds
        (2, vec![2, 1]),                    // wrap-around with small n
        (100, vec![1, 100]),                // max n, start < end
        (100, vec![100, 1]),                // max n, wrap-around
        (5, vec![3, 3 + 1]),               // start == end - 1
        (5, vec![1, 5, 1]),                // back and forth
        (10, vec![5, 8, 2, 9, 1]),         // multiple rounds
        (3, vec![1, 2, 3, 1, 2, 3]),       // full cycle
        (100, vec![50, 51]),               // middle of range
        (4, vec![4, 1]),                    // start == n, end == 1
    ];

    let mutation_kinds: Vec<u8> = (0..=8).collect();

    // Apply every mutation to examples
    for (n_val, rounds_val) in &examples {
        for &mk in &mutation_kinds {
            let (n_out, r_out) = mutate(*n_val, rounds_val.clone(), mk);
            emit(n_out, r_out, &mut seen, &mut out, &mut count);
        }
    }

    // Apply every mutation to hand-crafted seeds
    for (n_val, rounds_val) in &seeds {
        for &mk in &mutation_kinds {
            let (n_out, r_out) = mutate(*n_val, rounds_val.clone(), mk);
            emit(n_out, r_out, &mut seen, &mut out, &mut count);
        }
    }

    // Random test cases with diverse sizes
    while count < target {
        let n: i32 = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_i64(2, 5) as i32,     // tiny
            1 => rng.gen_range_i64(2, 10) as i32,    // small
            2 => rng.gen_range_i64(10, 50) as i32,   // medium
            3 => rng.gen_range_i64(50, 100) as i32,  // large
            _ => 100,                                  // max
        };
        let len: usize = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(2, 3),           // tiny
            1 => rng.gen_range_usize(2, 5),           // small
            2 => rng.gen_range_usize(5, 20),          // medium
            3 => rng.gen_range_usize(20, 50),         // large
            _ => rng.gen_range_usize(50, 101),        // max
        };
        let rounds_val = random_rounds(&mut rng, n, len);
        let mk = rng.gen_range_usize(0, 8) as u8;
        let (n_out, r_out) = mutate(n, rounds_val, mk);
        emit(n_out, r_out, &mut seen, &mut out, &mut count);
    }
}
