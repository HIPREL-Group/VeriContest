use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    customers: Vec<i32>,
    boarding_cost: i32,
    running_cost: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32, i32))
    requires
        1 <= customers.len() <= 100_000,
        forall|i: int| 0 <= i < customers.len() ==> 0 <= #[trigger] customers[i] <= 50,
        1 <= boarding_cost <= 100,
        1 <= running_cost <= 100,
    ensures
        1 <= result.0.len() <= 100_000,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 50,
        1 <= result.1 <= 100,
        1 <= result.2 <= 100,
{
    if mutation_kind == 0 {
        // identity
        (customers, boarding_cost, running_cost)
    } else if mutation_kind == 1 {
        // set first element to 0
        let mut c = customers;
        c.set(0, 0);
        (c, boarding_cost, running_cost)
    } else if mutation_kind == 2 {
        // set first element to 50 (max customers)
        let mut c = customers;
        c.set(0, 50);
        (c, boarding_cost, running_cost)
    } else if mutation_kind == 3 {
        // set last element to 0
        let mut c = customers;
        let last = c.len() - 1;
        c.set(last, 0);
        (c, boarding_cost, running_cost)
    } else if mutation_kind == 4 {
        // set last element to 50
        let mut c = customers;
        let last = c.len() - 1;
        c.set(last, 50);
        (c, boarding_cost, running_cost)
    } else if mutation_kind == 5 {
        // set all elements to 0
        let mut c = customers;
        let mut i: usize = 0;
        while i < c.len()
            invariant
                0 <= i <= c.len(),
                c.len() == customers.len(),
                1 <= c.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> c[j] == 0,
                forall|j: int| i <= j < c.len() ==> c[j] == customers[j],
            decreases c.len() - i,
        {
            c.set(i, 0);
            i += 1;
        }
        (c, boarding_cost, running_cost)
    } else if mutation_kind == 6 {
        // set all elements to 4 (exactly fills one gondola per rotation)
        let mut c = customers;
        let mut i: usize = 0;
        while i < c.len()
            invariant
                0 <= i <= c.len(),
                c.len() == customers.len(),
                1 <= c.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> c[j] == 4,
                forall|j: int| i <= j < c.len() ==> c[j] == customers[j],
            decreases c.len() - i,
        {
            c.set(i, 4);
            i += 1;
        }
        (c, boarding_cost, running_cost)
    } else if mutation_kind == 7 && customers.len() < 100_000 {
        // grow: append one element (0)
        let mut c = customers;
        c.push(0);
        (c, boarding_cost, running_cost)
    } else if mutation_kind == 8 && customers.len() > 1 {
        // shrink: pop last element
        let mut c = customers;
        c.pop();
        (c, boarding_cost, running_cost)
    } else if mutation_kind == 9 {
        // nudge first element up (if < 50)
        let mut c = customers;
        if c[0] < 50 {
            c.set(0, c[0] + 1);
        }
        (c, boarding_cost, running_cost)
    } else if mutation_kind == 10 {
        // nudge first element down (if > 0)
        let mut c = customers;
        if c[0] > 0 {
            c.set(0, c[0] - 1);
        }
        (c, boarding_cost, running_cost)
    } else if mutation_kind == 11 {
        // set boarding_cost to 1 (min)
        (customers, 1, running_cost)
    } else if mutation_kind == 12 {
        // set boarding_cost to 100 (max)
        (customers, 100, running_cost)
    } else if mutation_kind == 13 {
        // set running_cost to 1 (min)
        (customers, boarding_cost, 1)
    } else if mutation_kind == 14 {
        // set running_cost to 100 (max)
        (customers, boarding_cost, 100)
    } else if mutation_kind == 15 {
        // high boarding, low running (always profitable)
        (customers, 100, 1)
    } else if mutation_kind == 16 {
        // low boarding, high running (likely unprofitable)
        (customers, 1, 100)
    } else {
        // fallback: identity
        (customers, boarding_cost, running_cost)
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

fn mutate(customers: Vec<i32>, boarding_cost: i32, running_cost: i32, mutation_kind: u8) -> (Vec<i32>, i32, i32) {
    generate_test_case(customers, boarding_cost, running_cost, mutation_kind)
}

fn random_customers(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(0, 50) as i32);
    }
    v
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1599);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0usize;

    let mut emit = |customers: Vec<i32>, boarding_cost: i32, running_cost: i32,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, total: &mut usize| {
        if *total >= count { return; }
        let key = format!("{:?},{},{}", customers, boarding_cost, running_cost);
        if !seen.insert(key) { return; }
        let result = Solution::min_operations_max_profit(customers.clone(), boarding_cost, running_cost);
        writeln!(out, "{}", json!({
            "input": {"customers": customers, "boarding_cost": boarding_cost, "running_cost": running_cost},
            "output": result
        })).unwrap();
        *total += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, i32, i32)> = vec![
        (vec![8, 3], 5, 6),
        (vec![10, 9, 6], 6, 4),
        (vec![3, 4, 0, 5, 1], 1, 92),
    ];
    for (c, bc, rc) in examples {
        emit(c, bc, rc, &mut seen, &mut out, &mut total);
    }

    // Seed inputs: interesting cases
    let seed_customers: Vec<Vec<i32>> = vec![
        vec![0],
        vec![50],
        vec![4],
        vec![1],
        vec![0, 0, 0],
        vec![50, 50, 50],
        vec![4, 4, 4, 4],
        vec![1, 2, 3, 4, 5],
        vec![50, 0, 0, 0, 0],
        vec![0, 0, 0, 0, 50],
        vec![10, 10, 10, 10, 10, 10, 10, 10, 10, 10],
        vec![3],
        vec![0, 0],
    ];
    let seed_costs: Vec<(i32, i32)> = vec![
        (1, 1), (1, 100), (100, 1), (100, 100), (5, 6), (50, 50), (4, 1),
    ];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];

    // Cross-product: seeds × costs × mutations
    for cust in &seed_customers {
        for &(bc, rc) in &seed_costs {
            for &mk in &mutation_kinds {
                let (c, b, r) = mutate(cust.clone(), bc, rc, mk);
                emit(c, b, r, &mut seen, &mut out, &mut total);
            }
        }
    }

    // Random test cases with mutations
    for _ in 0..200 {
        if total >= count { break; }
        let len = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),       // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 1000),   // large
            _ => rng.gen_range_usize(1001, 10000), // very large
        };
        let cust = random_customers(&mut rng, len);
        let bc = rng.gen_range_i64(1, 100) as i32;
        let rc = rng.gen_range_i64(1, 100) as i32;
        let mk = rng.gen_range_usize(0, 16) as u8;
        let (c, b, r) = mutate(cust, bc, rc, mk);
        emit(c, b, r, &mut seen, &mut out, &mut total);
    }

    // Fill remaining with random identity
    while total < count {
        let len = rng.gen_range_usize(1, 1000);
        let cust = random_customers(&mut rng, len);
        let bc = rng.gen_range_i64(1, 100) as i32;
        let rc = rng.gen_range_i64(1, 100) as i32;
        emit(cust, bc, rc, &mut seen, &mut out, &mut total);
    }
}
