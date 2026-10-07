use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    candies: Vec<i32>,
    extra_candies: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        2 <= candies.len() <= 100,
        forall|i: int| 0 <= i < candies.len() ==> 1 <= #[trigger] candies[i] <= 100,
        1 <= extra_candies <= 50,
    ensures
        2 <= result.0.len() <= 100,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100,
        1 <= result.1 <= 50,
{
    if mutation_kind == 0 {
        // identity
        (candies, extra_candies)
    } else if mutation_kind == 1 {
        // flip first and last elements
        let mut c = candies;
        let last = c.len() - 1;
        let tmp = c[0];
        c.set(0, c[last]);
        c.set(last, tmp);
        (c, extra_candies)
    } else if mutation_kind == 2 {
        // set all candies to 1 (minimum)
        let mut c = candies;
        let mut i: usize = 0;
        while i < c.len()
            invariant
                0 <= i <= c.len(),
                c.len() == candies.len(),
                2 <= c.len() <= 100,
                forall|j: int| 0 <= j < i ==> #[trigger] c[j] == 1i32,
                forall|j: int| i <= j < c.len() ==> 1 <= #[trigger] c[j] <= 100,
            decreases c.len() - i,
        {
            c.set(i, 1);
            i += 1;
        }
        (c, extra_candies)
    } else if mutation_kind == 3 {
        // set all candies to 100 (maximum)
        let mut c = candies;
        let mut i: usize = 0;
        while i < c.len()
            invariant
                0 <= i <= c.len(),
                c.len() == candies.len(),
                2 <= c.len() <= 100,
                forall|j: int| 0 <= j < i ==> #[trigger] c[j] == 100i32,
                forall|j: int| i <= j < c.len() ==> 1 <= #[trigger] c[j] <= 100,
            decreases c.len() - i,
        {
            c.set(i, 100);
            i += 1;
        }
        (c, extra_candies)
    } else if mutation_kind == 4 {
        // set extra_candies to 1
        (candies, 1i32)
    } else if mutation_kind == 5 {
        // set extra_candies to 50
        (candies, 50i32)
    } else if mutation_kind == 6 && candies.len() < 100 {
        // grow by one element (push 1)
        let mut c = candies;
        c.push(1);
        (c, extra_candies)
    } else if mutation_kind == 7 && candies.len() > 2 {
        // shrink by one element (pop)
        let mut c = candies;
        let last_val = c[c.len() - 1];
        c.pop();
        (c, extra_candies)
    } else if mutation_kind == 8 {
        // set first element to 100, rest to 1
        let mut c = candies;
        let mut i: usize = 0;
        while i < c.len()
            invariant
                0 <= i <= c.len(),
                c.len() == candies.len(),
                2 <= c.len() <= 100,
                i == 0 ==> forall|j: int| 0 <= j < c.len() ==> 1 <= #[trigger] c[j] <= 100,
                i > 0 ==> #[trigger] c[0] == 100i32,
                i > 0 ==> forall|j: int| 1 <= j < i ==> #[trigger] c[j] == 1i32,
                i > 0 ==> forall|j: int| i <= j < c.len() ==> 1 <= #[trigger] c[j] <= 100,
            decreases c.len() - i,
        {
            if i == 0 {
                c.set(i, 100);
            } else {
                c.set(i, 1);
            }
            i += 1;
        }
        (c, extra_candies)
    } else {
        // fallback: identity
        (candies, extra_candies)
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

extern crate serde_json;
use serde_json::json;

fn random_candies(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(1, 100) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0usize;

    let mut emit = |candies: Vec<i32>, extra_candies: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, total: &mut usize| {
        if *total >= count { return; }
        let key = format!("{:?}:{}", candies, extra_candies);
        if !seen.insert(key) { return; }
        let result = Solution::kids_with_candies(candies.clone(), extra_candies);
        writeln!(out, "{}", json!({
            "input": {"candies": candies, "extraCandies": extra_candies},
            "output": result
        })).unwrap();
        *total += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![2, 3, 5, 1, 3], 3),
        (vec![4, 2, 1, 1, 2], 1),
        (vec![12, 1, 12], 10),
    ];
    for (candies, extra) in examples {
        emit(candies, extra, &mut seen, &mut out, &mut total);
    }

    // Edge case seeds
    let edge_seeds: Vec<(Vec<i32>, i32)> = vec![
        (vec![1, 1], 1),
        (vec![100, 100], 50),
        (vec![1, 100], 1),
        (vec![1, 100], 50),
        (vec![100, 1], 1),
        (vec![100, 1], 50),
        (vec![1, 1, 1], 1),
        (vec![50, 50, 50, 50], 25),
        (vec![1, 2, 3, 4, 5], 1),
        (vec![1, 2, 3, 4, 5], 4),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8];

    // Apply every mutation to every edge seed
    for (candies, extra) in &edge_seeds {
        for &mk in &mutation_kinds {
            let (c, e) = generate_test_case(candies.clone(), *extra, mk);
            emit(c, e, &mut seen, &mut out, &mut total);
        }
    }

    // Random test cases with diverse sizes
    while total < count {
        let n: usize = match total % 4 {
            0 => rng.gen_range_usize(2, 5),     // tiny
            1 => rng.gen_range_usize(2, 20),    // small
            2 => rng.gen_range_usize(21, 50),   // medium
            _ => rng.gen_range_usize(51, 100),  // max
        };
        let candies = random_candies(&mut rng, n);
        let extra = rng.gen_range_i64(1, 50) as i32;
        let mk = rng.gen_range_usize(0, 8) as u8;
        let (c, e) = generate_test_case(candies, extra, mk);
        emit(c, e, &mut seen, &mut out, &mut total);
    }
}
