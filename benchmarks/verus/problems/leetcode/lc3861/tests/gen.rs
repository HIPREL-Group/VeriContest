use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    capacity: Vec<i32>,
    item_size: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= capacity.len() <= 100,
        forall|k: int| 0 <= k < capacity.len() ==> 1 <= #[trigger] capacity[k] <= 100,
        1 <= item_size <= 100,
    ensures
        1 <= result.0.len() <= 100,
        forall|k: int| 0 <= k < result.0.len() ==> 1 <= #[trigger] result.0[k] <= 100,
        1 <= result.1 <= 100,
{
    if mutation_kind == 0 {
        // identity
        (capacity, item_size)
    } else if mutation_kind == 1 {
        // set first element to 1 (minimum capacity)
        let mut cap = capacity;
        cap.set(0, 1);
        (cap, item_size)
    } else if mutation_kind == 2 {
        // set first element to 100 (maximum capacity)
        let mut cap = capacity;
        cap.set(0, 100);
        (cap, item_size)
    } else if mutation_kind == 3 {
        // set all elements to item_size (all can fit exactly)
        let mut cap = capacity;
        let mut i: usize = 0;
        while i < cap.len()
            invariant
                0 <= i <= cap.len(),
                cap.len() == capacity.len(),
                1 <= cap.len() <= 100,
                1 <= item_size <= 100,
                forall|j: int| 0 <= j < i ==> #[trigger] cap[j] == item_size,
                forall|j: int| i <= j < cap.len() ==> #[trigger] cap[j] == capacity[j],
            decreases cap.len() - i,
        {
            cap.set(i, item_size);
            i += 1;
        }
        (cap, item_size)
    } else if mutation_kind == 4 && capacity.len() < 100 {
        // grow: push item_size as new element
        let mut cap = capacity;
        cap.push(item_size);
        (cap, item_size)
    } else if mutation_kind == 5 && capacity.len() > 1 {
        // shrink: pop last element
        let mut cap = capacity;
        cap.pop();
        (cap, item_size)
    } else if mutation_kind == 6 {
        // set item_size to 1 (everything fits)
        (capacity, 1)
    } else if mutation_kind == 7 {
        // set item_size to 100 (only cap[i]==100 fit)
        (capacity, 100)
    } else if mutation_kind == 8 {
        // set all elements to 1 (minimum capacity array)
        let mut cap = capacity;
        let mut i: usize = 0;
        while i < cap.len()
            invariant
                0 <= i <= cap.len(),
                cap.len() == capacity.len(),
                1 <= cap.len() <= 100,
                forall|j: int| 0 <= j < i ==> #[trigger] cap[j] == 1i32,
                forall|j: int| i <= j < cap.len() ==> #[trigger] cap[j] == capacity[j],
            decreases cap.len() - i,
        {
            cap.set(i, 1);
            i += 1;
        }
        (cap, item_size)
    } else if mutation_kind == 9 {
        // nudge item_size up if possible
        if item_size < 100 {
            (capacity, item_size + 1)
        } else {
            (capacity, item_size)
        }
    } else if mutation_kind == 10 {
        // nudge item_size down if possible
        if item_size > 1 {
            (capacity, item_size - 1)
        } else {
            (capacity, item_size)
        }
    } else if mutation_kind == 11 {
        // swap first and last elements
        if capacity.len() >= 2 {
            let mut cap = capacity;
            let last = cap.len() - 1;
            let first_val = cap[0];
            let last_val = cap[last];
            cap.set(0, last_val);
            cap.set(last, first_val);
            (cap, item_size)
        } else {
            (capacity, item_size)
        }
    } else {
        // fallback: identity
        (capacity, item_size)
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

fn mutate(capacity: Vec<i32>, item_size: i32, mutation_kind: u8) -> (Vec<i32>, i32) {
    generate_test_case(capacity, item_size, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_capacity(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut cap = Vec::with_capacity(len);
    for _ in 0..len {
        cap.push(rng.gen_range_i64(1, 100) as i32);
    }
    cap
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3861);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |capacity: Vec<i32>, item_size: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}:{}", capacity, item_size);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::minimum_index(capacity.clone(), item_size);
        writeln!(out, "{}", json!({"input": {"capacity": capacity, "itemSize": item_size}, "output": output})).unwrap();
        *count += 1;
    };

    // Example test cases from description.md
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![1, 5, 3, 7], 3),
        (vec![3, 5, 4, 3], 2),
        (vec![4], 5),
    ];
    for (cap, isz) in &examples {
        emit(cap.clone(), *isz, &mut seen, &mut out, &mut count);
    }

    // Hand-crafted seeds covering interesting cases
    let seeds: Vec<(Vec<i32>, i32)> = vec![
        (vec![1], 1),                       // single element, exact fit
        (vec![1], 2),                       // single element, no fit
        (vec![100], 100),                   // max capacity, max item
        (vec![100], 1),                     // max capacity, min item
        (vec![1, 2, 3, 4, 5], 3),           // ascending
        (vec![5, 4, 3, 2, 1], 3),           // descending
        (vec![3, 3, 3, 3], 3),              // all equal, exact fit
        (vec![3, 3, 3, 3], 4),              // all equal, no fit
        (vec![50, 1, 50], 50),              // min-cap at edges
        (vec![2, 1, 2], 2),                 // min-cap in middle not fitting
        (vec![10, 20, 10, 20], 15),         // alternating, some fit
        (vec![1, 1, 1, 1, 1, 1, 1, 1, 1, 1], 1), // all min
    ];

    let mutation_kinds: Vec<u8> = (0..=11).collect();

    // Apply every mutation to every seed
    for (cap, isz) in &seeds {
        for &mk in &mutation_kinds {
            let (rcap, risz) = mutate(cap.clone(), *isz, mk);
            emit(rcap, risz, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations across size classes
    while count < target_count {
        let n: usize = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),       // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 50),      // medium
            3 => rng.gen_range_usize(51, 100),     // large
            _ => rng.gen_range_usize(90, 100),     // max
        };
        let cap = random_capacity(&mut rng, n);
        let isz = match rng.gen_range_usize(0, 4) {
            0 => 1,                                // boundary min
            1 => 100,                              // boundary max
            2 => rng.gen_range_i64(1, 10) as i32,  // small
            _ => rng.gen_range_i64(1, 100) as i32, // full range
        };
        let mk = rng.gen_range_usize(0, 11) as u8;
        let (rcap, risz) = mutate(cap, isz, mk);
        emit(rcap, risz, &mut seen, &mut out, &mut count);
    }
}
