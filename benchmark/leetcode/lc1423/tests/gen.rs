use vstd::prelude::*;

verus! {

pub fn generate_test_case(card_points: Vec<i32>, seed_k: i32, mutation_kind: u8) -> (result: (Vec<i32>, i32))
    requires
        1 <= card_points.len() <= 100_000,
        forall|i: int| 0 <= i < card_points.len() ==> 1 <= #[trigger] card_points[i] <= 10_000,
        1 <= seed_k,
    ensures
        1 <= result.0.len(),
        result.0.len() <= 100_000,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 10_000,
        1 <= result.1,
        result.1 <= result.0.len(),
{
    // Clamp seed_k into valid range [1, card_points.len()]
    let len = card_points.len() as i32;
    let k: i32 = if seed_k > len { len } else { seed_k };

    if mutation_kind == 0 {
        // identity
        (card_points, k)
    } else if mutation_kind == 1 {
        // set last element to 1 (min boundary)
        let mut cp = card_points;
        let last = cp.len() - 1;
        cp.set(last, 1);
        (cp, k)
    } else if mutation_kind == 2 {
        // set last element to 10_000 (max boundary)
        let mut cp = card_points;
        let last = cp.len() - 1;
        cp.set(last, 10_000);
        (cp, k)
    } else if mutation_kind == 3 {
        // set first element to 1 (min boundary)
        let mut cp = card_points;
        cp.set(0, 1);
        (cp, k)
    } else if mutation_kind == 4 {
        // set first element to 10_000 (max boundary)
        let mut cp = card_points;
        cp.set(0, 10_000);
        (cp, k)
    } else if mutation_kind == 5 {
        // set all elements to 1
        let mut cp = card_points;
        let mut i: usize = 0;
        while i < cp.len()
            invariant
                0 <= i <= cp.len(),
                cp.len() == card_points.len(),
                1 <= cp.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> cp[j] == 1i32,
                forall|j: int| i <= j < cp.len() ==> cp[j] == card_points[j],
            decreases cp.len() - i,
        {
            cp.set(i, 1);
            i += 1;
        }
        (cp, k)
    } else if mutation_kind == 6 {
        // set all elements to 10_000
        let mut cp = card_points;
        let mut i: usize = 0;
        while i < cp.len()
            invariant
                0 <= i <= cp.len(),
                cp.len() == card_points.len(),
                1 <= cp.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> cp[j] == 10_000i32,
                forall|j: int| i <= j < cp.len() ==> cp[j] == card_points[j],
            decreases cp.len() - i,
        {
            cp.set(i, 10_000);
            i += 1;
        }
        (cp, k)
    } else if mutation_kind == 7 && card_points.len() < 100_000 {
        // grow by one element (push 1)
        let mut cp = card_points;
        cp.push(1);
        // k is still valid since len increased
        (cp, k)
    } else if mutation_kind == 8 && card_points.len() > 1 {
        // shrink by one element (pop)
        let mut cp = card_points;
        cp.pop();
        // k might exceed new length, clamp
        let new_len = cp.len() as i32;
        let new_k = if k > new_len { new_len } else { k };
        (cp, new_k)
    } else if mutation_kind == 9 {
        // set k = 1 (take minimum cards)
        (card_points, 1)
    } else if mutation_kind == 10 {
        // set k = card_points.len() (take all cards)
        (card_points, len)
    } else if mutation_kind == 11 && card_points.len() >= 2 {
        // swap first and last elements
        let mut cp = card_points;
        let last = cp.len() - 1;
        let tmp = cp[0];
        cp.set(0, cp[last]);
        cp.set(last, tmp);
        (cp, k)
    } else if mutation_kind == 12 {
        // nudge first element up (if < 10_000)
        let mut cp = card_points;
        if cp[0] < 10_000 {
            cp.set(0, cp[0] + 1);
        }
        (cp, k)
    } else if mutation_kind == 13 {
        // nudge last element down (if > 1)
        let mut cp = card_points;
        let last = cp.len() - 1;
        if cp[last] > 1 {
            cp.set(last, cp[last] - 1);
        }
        (cp, k)
    } else {
        // fallback: identity
        (card_points, k)
    }
}

} // verus!

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
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

fn random_card_points(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut cp = Vec::with_capacity(len);
    for _ in 0..len {
        cp.push(rng.gen_range_i64(1, 10_000) as i32);
    }
    cp
}

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

    let mut emit = |card_points: Vec<i32>, k: i32,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= goal { return; }
        let key = format!("{:?},{}", card_points, k);
        if !seen.insert(key) { return; }
        let output = Solution::max_score(card_points.clone(), k);
        writeln!(out, "{}", json!({"input": {"cardPoints": card_points, "k": k}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    emit(vec![1,2,3,4,5,6,1], 3, &mut seen, &mut out, &mut count);
    emit(vec![2,2,2], 2, &mut seen, &mut out, &mut count);
    emit(vec![9,7,7,9,7,7,9], 7, &mut seen, &mut out, &mut count);

    // Seed pool: interesting arrays
    let seed_arrays: Vec<Vec<i32>> = vec![
        vec![1],                             // single element
        vec![10_000],                        // single max
        vec![1, 1],                          // two min
        vec![10_000, 10_000],                // two max
        vec![1, 10_000],                     // min then max
        vec![10_000, 1],                     // max then min
        vec![5000, 5000, 5000],              // all same middle
        vec![1, 2, 3, 4, 5],                // ascending
        vec![5, 4, 3, 2, 1],                // descending
        vec![1, 1, 1, 1, 10_000],           // one big at end
        vec![10_000, 1, 1, 1, 1],           // one big at start
        vec![1, 1, 10_000, 1, 1],           // one big in middle
        vec![100, 200, 300, 400, 500, 600], // increasing moderate
    ];

    let mutation_kinds: Vec<u8> = (0..=14).collect();
    let k_strategies: Vec<Box<dyn Fn(usize) -> i32>> = vec![
        Box::new(|_len| 1i32),                              // k=1
        Box::new(|len| len as i32),                          // k=len
        Box::new(|len| ((len + 1) / 2) as i32),             // k=half
        Box::new(|len| if len >= 3 { 3 } else { len as i32 }), // k=3 or max
        Box::new(|len| if len >= 2 { 2 } else { 1 }),       // k=2 or 1
    ];

    // Apply mutations to seed arrays with different k strategies
    for s in &seed_arrays {
        for ks in &k_strategies {
            for &mk in &mutation_kinds {
                if count >= goal { break; }
                let k_val = ks(s.len());
                let (cp, k) = generate_test_case(s.clone(), k_val, mk);
                emit(cp, k, &mut seen, &mut out, &mut count);
            }
        }
    }

    // Random seeds with random mutations across size classes
    for i in 0..200 {
        if count >= goal { break; }
        let len = match i % 5 {
            0 => rng.gen_range_usize(1, 3),        // tiny
            1 => rng.gen_range_usize(1, 10),        // small
            2 => rng.gen_range_usize(11, 100),      // medium
            3 => rng.gen_range_usize(101, 1000),    // large
            _ => rng.gen_range_usize(1001, 10_000), // very large
        };
        let s = random_card_points(&mut rng, len);
        let k_val = rng.gen_range_i64(1, len as i64) as i32;
        let mk = rng.gen_range_usize(0, 14) as u8;
        let (cp, k) = generate_test_case(s, k_val, mk);
        emit(cp, k, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random seeds, identity mutation
    while count < goal {
        let len = rng.gen_range_usize(1, 5000);
        let s = random_card_points(&mut rng, len);
        let k_val = rng.gen_range_i64(1, len as i64) as i32;
        let (cp, k) = generate_test_case(s, k_val, 0);
        emit(cp, k, &mut seen, &mut out, &mut count);
    }
}
