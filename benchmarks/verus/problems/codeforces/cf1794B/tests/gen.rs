use vstd::prelude::*;

verus! {

pub open spec fn seq_elements_positive(s: Seq<i32>) -> bool {
    forall|i: int|
        #![trigger s[i]]
        0 <= i && i < s.len() ==> s[i] >= 1 && s[i] <= 1_000_000_000
}

pub fn generate_test_case(a: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= a.len() <= 10000,
        seq_elements_positive(a@),
    ensures
        1 <= result.len() <= 10000,
        seq_elements_positive(result@),
{
    if mutation_kind == 0 {
        // identity
        a
    } else if mutation_kind == 1 {
        // set first element to 1 (minimum boundary)
        let mut v = a;
        v.set(0, 1);
        v
    } else if mutation_kind == 2 {
        // set first element to 1_000_000_000 (maximum boundary)
        let mut v = a;
        v.set(0, 1_000_000_000);
        v
    } else if mutation_kind == 3 {
        // set last element to 1
        let mut v = a;
        let last = v.len() - 1;
        v.set(last, 1);
        v
    } else if mutation_kind == 4 {
        // set all elements to 1
        let mut v = a;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == a.len(),
                1 <= v.len() <= 10000,
                forall|j: int| #![trigger v@[j]] 0 <= j < i ==> v@[j] == 1,
                forall|j: int| #![trigger v@[j]] i <= j < v.len() ==> v@[j] == a@[j],
            decreases v.len() - i,
        {
            v.set(i, 1);
            i += 1;
        }
        v
    } else if mutation_kind == 5 && a.len() < 10000 {
        // grow by one element (push 1)
        let mut v = a;
        v.push(1);
        assert(v@.len() == a@.len() + 1);
        assert(forall|j: int| #![trigger v@[j]] 0 <= j < a@.len() ==> v@[j] == a@[j]);
        assert(v@[a@.len() as int] == 1);
        v
    } else if mutation_kind == 6 && a.len() > 1 {
        // shrink by one element (pop)
        let mut v = a;
        v.pop();
        assert(v@.len() == a@.len() - 1);
        assert(forall|j: int| #![trigger v@[j]] 0 <= j < v@.len() ==> v@[j] == a@[j]);
        v
    } else if mutation_kind == 7 {
        // nudge first element: if < 1_000_000_000, increment by 1
        let mut v = a;
        if v[0] < 1_000_000_000 {
            v.set(0, v[0] + 1);
        }
        v
    } else if mutation_kind == 8 {
        // nudge first element down: if > 1, decrement by 1
        let mut v = a;
        if v[0] > 1 {
            v.set(0, v[0] - 1);
        }
        v
    } else if mutation_kind == 9 {
        // set all elements to 1_000_000_000
        let mut v = a;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == a.len(),
                1 <= v.len() <= 10000,
                forall|j: int| #![trigger v@[j]] 0 <= j < i ==> v@[j] == 1_000_000_000,
                forall|j: int| #![trigger v@[j]] i <= j < v.len() ==> v@[j] == a@[j],
            decreases v.len() - i,
        {
            v.set(i, 1_000_000_000);
            i += 1;
        }
        v
    } else {
        a // fallback
    }
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

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }

    fn gen_u8(&mut self) -> u8 {
        (self.next_u64() % 256) as u8
    }
}

struct Solution;
include!("../code.rs");

fn mutate(a: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(a, mutation_kind)
}

fn random_array(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(1, 1_000_000_000) as i32);
    }
    v
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

    let mut emit = |a: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        let key = format!("{:?}", a);
        if *count >= goal || !seen.insert(key) {
            return;
        }
        let output = Solution::not_dividing_array(a.clone());
        writeln!(out, "{}", json!({"input": {"a": a}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![2, 4, 3, 6],
        vec![1, 2, 3],
        vec![4, 2],
    ];

    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count);
    }

    // Seed arrays with interesting patterns
    let seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![1, 1],
        vec![1, 1, 1, 1, 1],
        vec![1_000_000_000],
        vec![1_000_000_000, 1_000_000_000],
        vec![1, 2, 4, 8],
        vec![6, 3, 6, 3],
        vec![2, 2, 2, 2],
        vec![3, 9, 27],
        vec![1, 1_000_000_000],
        vec![7, 7, 7, 7, 7, 7, 7],
        vec![100, 10, 1],
        vec![5, 25, 125],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Apply every mutation to every seed
    for seed_arr in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed_arr.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random arrays with size classes and random mutations
    for i in 0..80 {
        if count >= goal { break; }
        let len = match i % 5 {
            0 => rng.gen_range_usize(1, 3),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 100),    // medium
            3 => rng.gen_range_usize(101, 1000),  // large
            _ => rng.gen_range_usize(1001, 5000), // very large
        };
        let arr = random_array(&mut rng, len);
        let mk = (rng.gen_u8()) % 10;
        let result = mutate(arr, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random arrays, identity mutation
    while count < goal {
        let len = rng.gen_range_usize(1, 10000);
        let arr = random_array(&mut rng, len);
        emit(mutate(arr, 0), &mut seen, &mut out, &mut count);
    }
}
