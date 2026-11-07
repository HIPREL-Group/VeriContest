use vstd::prelude::*;

verus! {

pub fn generate_test_case(raw: Vec<i32>) -> (result: Vec<i32>)
    ensures
        3 <= result.len() <= 1000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100000,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
{
    let end = if raw.len() > 1000 { 1000usize } else { raw.len() };
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0usize;
    while i < end
        invariant
            0 <= i <= end <= raw.len(), end <= 1000, result.len() <= i,
            forall|j: int| 0 <= j < result.len() ==> 1 <= #[trigger] result[j] <= 100000,
            forall|j: int, k: int| 0 <= j < k < result.len() ==> result[j] != result[k],
        decreases end - i,
    {
        let v = raw[i];
        let v = if v < 1 { 1 } else if v > 100000 { 100000 } else { v };
        let mut j = 0usize;
        let mut found = false;
        while j < result.len()
            invariant
                0 <= j <= result.len(),
                !found ==> forall|k: int| 0 <= k < j ==> #[trigger] result[k] != v,
            decreases result.len() - j,
        {
            if result[j] == v { found = true; }
            j += 1;
        }
        if !found { result.push(v); }
        i += 1;
    }
    if result.len() < 3 {
        let mut fallback: Vec<i32> = Vec::new();
        fallback.push(1);
        fallback.push(2);
        fallback.push(3);
        fallback
    } else {
        result
    }
}


pub fn generate_candidate(
    rating: Vec<i32>,
    mutation_kind: u8,
) -> (result: Vec<i32>)
    requires
        3 <= rating.len() <= 1000,
        forall|i: int| 0 <= i < rating.len() ==> 1 <= (#[trigger] rating[i]) <= 100000,
    ensures
        3 <= result.len() <= 1000,
        forall|x: int| 0 <= x < result.len() ==> 1 <= #[trigger] result[x] <= 100000,
{
    if mutation_kind == 0 {
        // identity
        rating
    } else if mutation_kind == 1 {
        // set all elements to 1
        let mut a = rating;
        let mut i: usize = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                a.len() == rating.len(),
                3 <= a.len() <= 1000,
                forall|j: int| 0 <= j < i ==> a[j] == 1i32,
                forall|j: int| i <= j < a.len() ==> a[j] == rating[j],
            decreases a.len() - i,
        {
            a.set(i, 1);
            i += 1;
        }
        a
    } else if mutation_kind == 2 {
        // set all elements to max value
        let mut a = rating;
        let mut i: usize = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                a.len() == rating.len(),
                3 <= a.len() <= 1000,
                forall|j: int| 0 <= j < i ==> a[j] == 100000i32,
                forall|j: int| i <= j < a.len() ==> a[j] == rating[j],
            decreases a.len() - i,
        {
            a.set(i, 100000);
            i += 1;
        }
        a
    } else if mutation_kind == 3 {
        // make strictly increasing: rating[i] = i + 1
        let mut a = rating;
        let n = a.len();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == a.len(),
                a.len() == rating.len(),
                3 <= a.len() <= 1000,
                n <= 1000,
                forall|j: int| 0 <= j < i ==> a[j] == (j + 1) as i32,
                forall|j: int| i <= j < a.len() ==> a[j] == rating[j],
            decreases n - i,
        {
            a.set(i, (i + 1) as i32);
            i += 1;
        }
        a
    } else if mutation_kind == 4 {
        // make strictly decreasing: rating[i] = n - i
        let mut a = rating;
        let n = a.len();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == a.len(),
                a.len() == rating.len(),
                3 <= a.len() <= 1000,
                n <= 1000,
                forall|j: int| 0 <= j < i ==> a[j] == (n - j) as i32,
                forall|j: int| i <= j < a.len() ==> a[j] == rating[j],
            decreases n - i,
        {
            a.set(i, (n - i) as i32);
            i += 1;
        }
        a
    } else if mutation_kind == 5 && rating.len() < 1000 {
        // grow by one element
        let mut a = rating;
        a.push(1);
        a
    } else if mutation_kind == 6 && rating.len() > 3 {
        // shrink by one element
        let mut a = rating;
        a.pop();
        a
    } else if mutation_kind == 7 {
        // set first element to boundary value 1
        let mut a = rating;
        a.set(0, 1);
        a
    } else if mutation_kind == 8 {
        // set last element to boundary value 100000
        let mut a = rating;
        let last = a.len() - 1;
        a.set(last, 100000);
        a
    } else if mutation_kind == 9 {
        // set first to max, last to min
        let mut a = rating;
        a.set(0, 100000);
        let last = a.len() - 1;
        a.set(last, 1);
        a
    } else {
        // fallback: identity
        rating
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

fn random_rating(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(1, 100000) as i32);
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

    let mut emit = |rating: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, total: &mut usize| {
        let rating = generate_test_case(rating);
        if *total >= count { return; }
        let key = format!("{:?}", rating);
        if !seen.insert(key) { return; }
        let result = Solution::num_teams(rating.clone());
        writeln!(out, "{}", json!({
            "input": {"rating": rating},
            "output": result
        })).unwrap();
        *total += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![2, 5, 3, 4, 1],
        vec![2, 1, 3],
        vec![1, 2, 3, 4],
    ];
    for rating in examples {
        emit(rating, &mut seen, &mut out, &mut total);
    }

    // Edge case seeds
    let edge_seeds: Vec<Vec<i32>> = vec![
        vec![1, 2, 3],
        vec![3, 2, 1],
        vec![1, 3, 2],
        vec![2, 1, 3],
        vec![3, 1, 2],
        vec![1, 1, 1],
        vec![100000, 99999, 99998],
        vec![1, 2, 3, 4, 5],
        vec![5, 4, 3, 2, 1],
        vec![1, 100000, 50000],
        vec![50000, 1, 100000],
        vec![10, 20, 30, 40, 50, 60, 70, 80, 90, 100],
        vec![100, 90, 80, 70, 60, 50, 40, 30, 20, 10],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    for rating in &edge_seeds {
        for &mk in &mutation_kinds {
            let r = generate_candidate(rating.clone(), mk);
            emit(r, &mut seen, &mut out, &mut total);
        }
    }

    // Random test cases with diverse sizes
    while total < count {
        let n: usize = match total % 5 {
            0 => rng.gen_range_usize(3, 5),        // tiny
            1 => rng.gen_range_usize(3, 20),       // small
            2 => rng.gen_range_usize(21, 100),     // medium
            3 => rng.gen_range_usize(101, 500),    // large
            _ => rng.gen_range_usize(501, 1000),   // max
        };
        let rating = random_rating(&mut rng, n);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let r = generate_candidate(rating, mk);
        emit(r, &mut seen, &mut out, &mut total);
    }
}
