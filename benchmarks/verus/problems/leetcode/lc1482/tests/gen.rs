use vstd::prelude::*;

verus! {

pub fn bounded_values(values: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        1 <= result.len() <= 100000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1000000000,
{
    let n = if values.len() == 0 { 1usize } else if values.len() > 100000 { 100000usize } else { values.len() };
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 100000, 0 <= i <= n, result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> 1 <= #[trigger] result[j] <= 1000000000,
        decreases n - i,
    {
        let value = if i < values.len() { values[i] } else { 1 };
        result.push(if value < 1 { 1 } else if value > 1000000000 { 1000000000 } else { value });
        i += 1;
    }
    result
}

pub fn generate_test_case(bloom_day: Vec<i32>, m: i32, k: i32) -> (result: (Vec<i32>, i32, i32))
    ensures
        1 <= result.0.len() <= 100000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1000000000,
        1 <= result.1 <= 1000000,
        1 <= result.2 <= result.0.len(),
{
    let bloom_day = bounded_values(&bloom_day);
    let m = if m < 1 { 1 } else if m > 1000000 { 1000000 } else { m };
    let k = if k < 1 { 1 } else if k as usize > bloom_day.len() { bloom_day.len() as i32 } else { k };
    (bloom_day, m, k)
}


pub fn generate_candidate(
    bloom_day: Vec<i32>,
    m_val: i32,
    k_val: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32, i32))
    requires
        1 <= bloom_day.len() <= 100_000,
        forall|i: int| 0 <= i < bloom_day.len() ==> 1 <= #[trigger] bloom_day[i] <= 1_000_000_000,
        1 <= m_val <= 1_000_000,
        1 <= k_val <= bloom_day.len(),
    ensures
        1 <= result.0.len() <= 100_000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1_000_000_000,
        1 <= result.1 <= 1_000_000,
        1 <= result.2 <= result.0.len(),
{
    if mutation_kind == 0 {
        // identity
        (bloom_day, m_val, k_val)
    } else if mutation_kind == 1 {
        // set all bloom days to 1 (min value)
        let mut b = bloom_day;
        let mut i: usize = 0;
        while i < b.len()
            invariant
                0 <= i <= b.len(),
                b.len() == bloom_day.len(),
                1 <= b.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> b[j] == 1i32,
                forall|j: int| i <= j < b.len() ==> b[j] == bloom_day[j],
                forall|j: int| 0 <= j < bloom_day.len() ==> 1 <= #[trigger] bloom_day[j] <= 1_000_000_000,
            decreases b.len() - i,
        {
            b.set(i, 1);
            i += 1;
        }
        (b, m_val, k_val)
    } else if mutation_kind == 2 {
        // set all bloom days to max value
        let mut b = bloom_day;
        let mut i: usize = 0;
        while i < b.len()
            invariant
                0 <= i <= b.len(),
                b.len() == bloom_day.len(),
                1 <= b.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> b[j] == 1_000_000_000i32,
                forall|j: int| i <= j < b.len() ==> b[j] == bloom_day[j],
                forall|j: int| 0 <= j < bloom_day.len() ==> 1 <= #[trigger] bloom_day[j] <= 1_000_000_000,
            decreases b.len() - i,
        {
            b.set(i, 1_000_000_000i32);
            i += 1;
        }
        (b, m_val, k_val)
    } else if mutation_kind == 3 {
        // set k to 1
        (bloom_day, m_val, 1i32)
    } else if mutation_kind == 4 {
        // set k to bloom_day.len()
        let k = bloom_day.len() as i32;
        (bloom_day, m_val, k)
    } else if mutation_kind == 5 {
        // set m to 1
        (bloom_day, 1i32, k_val)
    } else if mutation_kind == 6 && bloom_day.len() < 100_000 {
        // grow array by one element (push 1)
        let mut b = bloom_day;
        b.push(1i32);
        (b, m_val, k_val)
    } else if mutation_kind == 7 && bloom_day.len() > 1 && (k_val as usize) < bloom_day.len() {
        // shrink array by one element (pop)
        let mut b = bloom_day;
        b.pop();
        (b, m_val, k_val)
    } else if mutation_kind == 8 {
        // set last element to 1
        let mut b = bloom_day;
        let last = b.len() - 1;
        b.set(last, 1i32);
        (b, m_val, k_val)
    } else if mutation_kind == 9 {
        // set last element to max
        let mut b = bloom_day;
        let last = b.len() - 1;
        b.set(last, 1_000_000_000i32);
        (b, m_val, k_val)
    } else if mutation_kind == 10 {
        // set m to m_val, k to 1, so m*k = m_val <= len is likely
        (bloom_day, m_val, 1i32)
    } else {
        // fallback: identity
        (bloom_day, m_val, k_val)
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

fn random_bloom_day(rng: &mut Rng, len: usize) -> Vec<i32> {
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
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0usize;

    let mut emit = |bloom_day: Vec<i32>, m: i32, k: i32,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    total: &mut usize| {
        let (bloom_day, m, k) = generate_test_case(bloom_day, m, k);
        if *total >= count { return; }
        let key = format!("{:?}:{}:{}", bloom_day, m, k);
        if !seen.insert(key) { return; }
        let result = Solution::min_days(bloom_day.clone(), m, k);
        writeln!(out, "{}", json!({
            "input": {"bloomDay": bloom_day, "m": m, "k": k},
            "output": result
        })).unwrap();
        *total += 1;
    };

    // Example inputs from description.md
    emit(vec![1,10,3,10,2], 3, 1, &mut seen, &mut out, &mut total);
    emit(vec![1,10,3,10,2], 3, 2, &mut seen, &mut out, &mut total);
    emit(vec![7,7,7,7,12,7,7], 2, 3, &mut seen, &mut out, &mut total);

    // Edge case seeds
    let edge_seeds: Vec<(Vec<i32>, i32, i32)> = vec![
        (vec![1], 1, 1),
        (vec![1_000_000_000], 1, 1),
        (vec![1, 1, 1], 1, 1),
        (vec![1, 1, 1], 1, 3),
        (vec![1, 1, 1], 3, 1),
        (vec![1, 2, 3, 4, 5], 2, 2),
        (vec![5, 4, 3, 2, 1], 2, 2),
        (vec![1, 1, 1, 1, 1], 5, 1),
        (vec![1, 1, 1, 1, 1], 1, 5),
        (vec![1000000000, 1000000000], 1, 1),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

    for (bd, m, k) in &edge_seeds {
        for &mk in &mutation_kinds {
            let (bd_out, m_out, k_out) = generate_candidate(bd.clone(), *m, *k, mk);
            emit(bd_out, m_out, k_out, &mut seen, &mut out, &mut total);
        }
    }

    // Random test cases with diverse sizes
    while total < count {
        let n: usize = match total % 5 {
            0 => rng.gen_range_usize(1, 5),          // tiny
            1 => rng.gen_range_usize(1, 20),         // small
            2 => rng.gen_range_usize(21, 200),       // medium
            3 => rng.gen_range_usize(201, 5000),     // large
            _ => rng.gen_range_usize(5001, 50_000),  // max
        };
        let bd = random_bloom_day(&mut rng, n);
        let k = rng.gen_range_usize(1, n) as i32;
        let m_max = std::cmp::min(1_000_000i64, n as i64) as i32;
        let m = rng.gen_range_i64(1, m_max as i64) as i32;
        let mk = rng.gen_range_usize(0, 10) as u8;
        let (bd_out, m_out, k_out) = generate_candidate(bd, m, k, mk);
        emit(bd_out, m_out, k_out, &mut seen, &mut out, &mut total);
    }
}
