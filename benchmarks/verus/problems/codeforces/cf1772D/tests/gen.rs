use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    elems: Vec<i32>,
    mutation_kind: u8,
) -> (result: Vec<i32>)
    requires
        2 <= elems.len() <= 200000,
        forall|i: int| 0 <= i < elems.len() as int ==> 0 <= #[trigger] elems[i] <= 1000000000,
    ensures
        2 <= result.len() <= 200000,
        forall|i: int| 0 <= i < result.len() as int ==> 0 <= #[trigger] result[i] <= 1000000000,
{
    if mutation_kind == 0 {
        // identity
        elems
    } else if mutation_kind == 1 && elems.len() < 200000 {
        // grow: append element with value 0
        let mut d = elems;
        d.push(0);
        d
    } else if mutation_kind == 2 && elems.len() > 2 {
        // shrink: remove last element
        let mut d = elems;
        d.pop();
        d
    } else if mutation_kind == 3 {
        // set first element to 0 (minimum boundary)
        let mut d = elems;
        d.set(0, 0);
        d
    } else if mutation_kind == 4 {
        // set first element to max boundary
        let mut d = elems;
        d.set(0, 1_000_000_000);
        d
    } else if mutation_kind == 5 {
        // set last element to 0
        let mut d = elems;
        let last = d.len() - 1;
        d.set(last, 0);
        d
    } else if mutation_kind == 6 {
        // set last element to max boundary
        let mut d = elems;
        let last = d.len() - 1;
        d.set(last, 1_000_000_000);
        d
    } else if mutation_kind == 7 {
        // set all elements to 0
        let mut d = elems;
        let ghost old_len = d.len();
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == old_len,
                2 <= d.len() <= 200000,
                forall|j: int| 0 <= j < i ==> d[j] == 0i32,
                forall|j: int| i <= j < d.len() as int
                    ==> 0 <= #[trigger] d[j] && d[j] <= 1_000_000_000,
            decreases d.len() - i,
        {
            d.set(i, 0);
            i += 1;
        }
        d
    } else if mutation_kind == 8 {
        // set all elements to max boundary
        let mut d = elems;
        let ghost old_len = d.len();
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == old_len,
                2 <= d.len() <= 200000,
                forall|j: int| 0 <= j < i ==> d[j] == 1_000_000_000i32,
                forall|j: int| i <= j < d.len() as int
                    ==> 0 <= #[trigger] d[j] && d[j] <= 1_000_000_000,
            decreases d.len() - i,
        {
            d.set(i, 1_000_000_000);
            i += 1;
        }
        d
    } else if mutation_kind == 9 && elems.len() >= 2 {
        // swap first and last elements
        let mut d = elems;
        let last = d.len() - 1;
        let first_val = d[0];
        let last_val = d[last];
        d.set(0, last_val);
        d.set(last, first_val);
        d
    } else if mutation_kind == 10 {
        // nudge first element up (if room)
        let mut d = elems;
        if d[0] < 1_000_000_000 {
            d.set(0, d[0] + 1);
        }
        d
    } else if mutation_kind == 11 {
        // nudge first element down (if room)
        let mut d = elems;
        if d[0] > 0 {
            d.set(0, d[0] - 1);
        }
        d
    } else {
        // fallback: identity
        elems
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

fn mutate(elems: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(elems, mutation_kind)
}

fn random_array(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(0, 1_000_000_000) as i32);
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
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let num_mutations: u8 = 12;

    let mut emit = |a: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let key = format!("{:?}", a);
        if !seen.insert(key) { return; }
        let output = Solution::absolute_sorting(a.clone());
        writeln!(out, "{}", json!({"input": {"a": a}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![5, 3, 7, 6],
    ];

    for ex in examples {
        for mk in 0..num_mutations {
            emit(mutate(ex.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }

    // Size classes for array lengths
    while count < target {
        let n: usize = match count % 5 {
            0 => rng.gen_range_usize(2, 5),        // tiny
            1 => rng.gen_range_usize(2, 10),        // small
            2 => rng.gen_range_usize(11, 100),      // medium
            3 => rng.gen_range_usize(101, 1000),    // large
            _ => rng.gen_range_usize(1001, 5000),   // big (capped for speed)
        };

        let a = random_array(&mut rng, n);
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        emit(mutate(a, mk), &mut seen, &mut out, &mut count);
    }
}
