use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    a: Vec<i64>,
    b: Vec<i64>,
    mutation_kind: u8,
) -> (result: (Vec<i64>, Vec<i64>))
    requires
        a.len() == b.len(),
        a.len() >= 1,
        forall|i: int| 0 <= i < a.len() ==> (#[trigger] a@[i] == 0 || a@[i] == 1),
        forall|i: int| 0 <= i < b.len() ==> (#[trigger] b@[i] == 0 || b@[i] == 1),
    ensures
        result.0.len() == result.1.len(),
        result.0.len() >= 1,
        forall|i: int| 0 <= i < result.0.len() ==> (#[trigger] result.0@[i] == 0 || result.0@[i] == 1),
        forall|i: int| 0 <= i < result.1.len() ==> (#[trigger] result.1@[i] == 0 || result.1@[i] == 1),
{
    if mutation_kind == 0 {
        // identity
        (a, b)
    } else if mutation_kind == 1 {
        // flip first element of a
        let mut a2 = a;
        let v = if a2[0] == 0 { 1i64 } else { 0i64 };
        a2.set(0, v);
        (a2, b)
    } else if mutation_kind == 2 {
        // flip first element of b
        let mut b2 = b;
        let v = if b2[0] == 0 { 1i64 } else { 0i64 };
        b2.set(0, v);
        (a, b2)
    } else if mutation_kind == 3 {
        // set all of a to 0
        let n = a.len();
        let mut a2 = a;
        let mut i: usize = 0;
        while i < n
            invariant
                n == a2.len(),
                n == b.len(),
                n >= 1,
                0 <= i <= n,
                forall|j: int| 0 <= j < i ==> a2@[j] == 0,
                forall|j: int| i <= j < n ==> (#[trigger] a2@[j] == 0 || a2@[j] == 1),
                forall|j: int| 0 <= j < b.len() ==> (#[trigger] b@[j] == 0 || b@[j] == 1),
            decreases n - i,
        {
            a2.set(i, 0i64);
            i += 1;
        }
        (a2, b)
    } else if mutation_kind == 4 {
        // set all of b to 0
        let n = b.len();
        let mut b2 = b;
        let mut i: usize = 0;
        while i < n
            invariant
                n == a.len(),
                n == b2.len(),
                n >= 1,
                0 <= i <= n,
                forall|j: int| 0 <= j < i ==> b2@[j] == 0,
                forall|j: int| i <= j < n ==> (#[trigger] b2@[j] == 0 || b2@[j] == 1),
                forall|j: int| 0 <= j < a.len() ==> (#[trigger] a@[j] == 0 || a@[j] == 1),
            decreases n - i,
        {
            b2.set(i, 0i64);
            i += 1;
        }
        (a, b2)
    } else if mutation_kind == 5 {
        // set all of a to 1
        let n = a.len();
        let mut a2 = a;
        let mut i: usize = 0;
        while i < n
            invariant
                n == a2.len(),
                n == b.len(),
                n >= 1,
                0 <= i <= n,
                forall|j: int| 0 <= j < i ==> a2@[j] == 1,
                forall|j: int| i <= j < n ==> (#[trigger] a2@[j] == 0 || a2@[j] == 1),
                forall|j: int| 0 <= j < b.len() ==> (#[trigger] b@[j] == 0 || b@[j] == 1),
            decreases n - i,
        {
            a2.set(i, 1i64);
            i += 1;
        }
        (a2, b)
    } else if mutation_kind == 6 {
        // set all of b to 1
        let n = b.len();
        let mut b2 = b;
        let mut i: usize = 0;
        while i < n
            invariant
                n == a.len(),
                n == b2.len(),
                n >= 1,
                0 <= i <= n,
                forall|j: int| 0 <= j < i ==> b2@[j] == 1,
                forall|j: int| i <= j < n ==> (#[trigger] b2@[j] == 0 || b2@[j] == 1),
                forall|j: int| 0 <= j < a.len() ==> (#[trigger] a@[j] == 0 || a@[j] == 1),
            decreases n - i,
        {
            b2.set(i, 1i64);
            i += 1;
        }
        (a, b2)
    } else if mutation_kind == 7 {
        // make a == b (all xor_val == 0, result is true)
        (a.clone(), a)
    } else if mutation_kind == 8 {
        // swap a and b
        (b, a)
    } else {
        // fallback: identity
        (a, b)
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

fn mutate(a: Vec<i64>, b: Vec<i64>, mutation_kind: u8) -> (Vec<i64>, Vec<i64>) {
    generate_test_case(a, b, mutation_kind)
}

fn random_binary_vec(rng: &mut Rng, len: usize) -> Vec<i64> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(0, 1));
    }
    v
}

extern crate serde_json;
use serde_json::json;

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

    let mut emit = |a: Vec<i64>, b: Vec<i64>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, total: &mut usize| {
        if *total >= count {
            return;
        }
        let key = format!("{:?}|{:?}", a, b);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::is_complementary_xor_possible(a.clone(), b.clone());
        writeln!(out, "{}", json!({
            "input": {"a": a, "b": b},
            "output": output
        })).unwrap();
        *total += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<i64>, Vec<i64>)> = vec![
        (vec![0, 1, 0], vec![1, 0, 1]),
        (vec![1, 1], vec![1, 0]),
        (vec![0, 0, 0, 0], vec![0, 0, 1, 1]),
        (vec![1, 0], vec![1, 0]),
        (vec![1, 1, 1], vec![1, 1, 1]),
    ];

    for (a, b) in &examples {
        let (ra, rb) = mutate(a.clone(), b.clone(), 0);
        emit(ra, rb, &mut seen, &mut out, &mut total);
    }

    // Hand-crafted seed inputs
    let seeds: Vec<(Vec<i64>, Vec<i64>)> = vec![
        (vec![0], vec![0]),
        (vec![1], vec![1]),
        (vec![0], vec![1]),
        (vec![1], vec![0]),
        (vec![0, 0], vec![0, 0]),
        (vec![1, 1], vec![1, 1]),
        (vec![0, 1], vec![1, 0]),
        (vec![1, 0, 1, 0], vec![0, 1, 0, 1]),
        (vec![0, 0, 0, 0, 0], vec![1, 1, 1, 1, 1]),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8];

    for (a, b) in &seeds {
        for &mk in &mutation_kinds {
            let (ra, rb) = mutate(a.clone(), b.clone(), mk);
            emit(ra, rb, &mut seen, &mut out, &mut total);
        }
    }

    // Random inputs with random mutations across diverse size classes
    while total < count {
        let n: usize = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 50),
            3 => rng.gen_range_usize(51, 200),
            _ => rng.gen_range_usize(201, 500),
        };
        let a = random_binary_vec(&mut rng, n);
        let b = random_binary_vec(&mut rng, n);
        let mk = rng.gen_range_usize(0, 8) as u8;
        let (ra, rb) = mutate(a, b, mk);
        emit(ra, rb, &mut seen, &mut out, &mut total);
    }
}
