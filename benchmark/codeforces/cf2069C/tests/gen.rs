use vstd::prelude::*;

verus! {

pub fn generate_test_case(a: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        3 <= a.len() <= 200_000,
        forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 3,
    ensures
        3 <= a.len() <= 200_000,
        forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 3,
        3 <= result.len() <= 200_000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 3,
{
    if mutation_kind == 0 {
        // identity
        a
    } else if mutation_kind == 1 {
        // set all elements to 1
        let mut d = a;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == a.len(),
                3 <= d.len() <= 200_000,
                forall|j: int| 0 <= j < i ==> d[j] == 1,
                forall|j: int| i <= j < d.len() ==> 1 <= #[trigger] d[j] <= 3,
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        d
    } else if mutation_kind == 2 {
        // set all elements to 2
        let mut d = a;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == a.len(),
                3 <= d.len() <= 200_000,
                forall|j: int| 0 <= j < i ==> d[j] == 2,
                forall|j: int| i <= j < d.len() ==> 1 <= #[trigger] d[j] <= 3,
            decreases d.len() - i,
        {
            d.set(i, 2);
            i += 1;
        }
        d
    } else if mutation_kind == 3 {
        // set all elements to 3
        let mut d = a;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == a.len(),
                3 <= d.len() <= 200_000,
                forall|j: int| 0 <= j < i ==> d[j] == 3,
                forall|j: int| i <= j < d.len() ==> 1 <= #[trigger] d[j] <= 3,
            decreases d.len() - i,
        {
            d.set(i, 3);
            i += 1;
        }
        d
    } else if mutation_kind == 4 {
        // set first element to 1
        let mut d = a;
        d.set(0, 1);
        d
    } else if mutation_kind == 5 {
        // set last element to 3
        let mut d = a;
        let last = d.len() - 1;
        d.set(last, 3);
        d
    } else if mutation_kind == 6 && a.len() < 200_000 {
        // grow by one element (push a 2)
        let mut d = a;
        d.push(2);
        d
    } else if mutation_kind == 7 && a.len() > 3 {
        // shrink by one element (pop)
        let mut d = a;
        d.pop();
        d
    } else if mutation_kind == 8 {
        // set pattern: first=1, middle=2, last=3
        let mut d = a;
        d.set(0, 1);
        let mid = d.len() / 2;
        d.set(mid, 2);
        let last = d.len() - 1;
        d.set(last, 3);
        d
    } else if mutation_kind == 9 && a.len() >= 4 {
        // swap first two elements
        let mut d = a;
        let v0 = d[0];
        let v1 = d[1];
        d.set(0, v1);
        d.set(1, v0);
        d
    } else {
        // fallback: identity
        a
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
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

extern crate serde_json;
use serde_json::json;

fn random_array(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut arr = Vec::with_capacity(len);
    for _ in 0..len {
        arr.push(rng.gen_range_usize(1, 3) as i32);
    }
    arr
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

    let mut emit = |a: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, total: &mut usize| {
        if *total >= count { return; }
        let key = format!("{:?}", a);
        if !seen.insert(key) { return; }
        let output = Solution::count_beautiful_subsequences(a.clone());
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        let inp_str = format!("1\n{}\n{}\n", a.len(), parts.join(" "));
        let out_str = format!("{}\n", output);
        writeln!(out, "{}", json!({"input": inp_str, "output": out_str})).unwrap();
        *total += 1;
    };

    // Example inputs from the problem description
    let examples: Vec<Vec<i32>> = vec![
        vec![3, 2, 1, 2, 2, 1, 3],
        vec![3, 1, 2, 2],
        vec![1, 2, 3],
        vec![1, 2, 3, 2, 1, 3, 2, 2, 3],
    ];
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut total);
    }

    // Seed arrays with mutations
    let seeds: Vec<Vec<i32>> = vec![
        vec![1, 2, 3],
        vec![1, 1, 1],
        vec![2, 2, 2],
        vec![3, 3, 3],
        vec![1, 1, 3],
        vec![1, 2, 2, 3],
        vec![1, 2, 3, 1, 2, 3],
        vec![1, 1, 2, 2, 3, 3],
        vec![3, 2, 1],
        vec![1, 2, 2, 2, 3],
    ];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = generate_test_case(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut total);
        }
    }

    // Size classes with random arrays and mutations
    let size_classes: Vec<(usize, usize)> = vec![
        (3, 5),       // tiny
        (3, 10),      // small
        (11, 50),     // medium
        (51, 200),    // large
        (201, 1000),  // larger
    ];
    for &(lo, hi) in &size_classes {
        for _ in 0..8 {
            if total >= count { break; }
            let n = rng.gen_range_usize(lo, hi);
            let arr = random_array(&mut rng, n);
            let mk = rng.gen_range_usize(0, 9) as u8;
            let result = generate_test_case(arr, mk);
            emit(result, &mut seen, &mut out, &mut total);
        }
    }

    // Fill remaining with random arrays, identity mutation
    while total < count {
        let n = match total % 5 {
            0 => rng.gen_range_usize(3, 5),
            1 => rng.gen_range_usize(3, 10),
            2 => rng.gen_range_usize(11, 50),
            3 => rng.gen_range_usize(51, 200),
            _ => rng.gen_range_usize(201, 1000),
        };
        let arr = random_array(&mut rng, n);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = generate_test_case(arr, mk);
        emit(result, &mut seen, &mut out, &mut total);
    }
}
