use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    customers: Vec<i32>,
    grumpy: Vec<i32>,
    minutes: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>, i32))
    requires
        customers.len() == grumpy.len(),
        1 <= minutes <= customers.len() <= 20_000,
        forall|i: int| 0 <= i < customers.len() ==> 0 <= #[trigger] customers[i] <= 1000,
        forall|i: int| 0 <= i < grumpy.len() ==> (#[trigger] grumpy[i] == 0 || grumpy[i] == 1),
    ensures
        result.0.len() == result.1.len(),
        1 <= result.2 <= result.0.len() <= 20_000,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 1000,
        forall|i: int| 0 <= i < result.1.len() ==> (#[trigger] result.1[i] == 0 || result.1[i] == 1),
{
    if mutation_kind == 0 {
        // identity
        (customers, grumpy, minutes)
    } else if mutation_kind == 1 {
        // set first customer to 0
        let mut c = customers;
        c.set(0, 0);
        (c, grumpy, minutes)
    } else if mutation_kind == 2 {
        // set first customer to 1000
        let mut c = customers;
        c.set(0, 1000);
        (c, grumpy, minutes)
    } else if mutation_kind == 3 {
        // flip first grumpy value
        let mut g = grumpy;
        let v: i32 = if g[0] == 0 { 1 } else { 0 };
        g.set(0, v);
        (customers, g, minutes)
    } else if mutation_kind == 4 {
        // set all grumpy to 0
        let mut g = grumpy;
        let mut i: usize = 0;
        while i < g.len()
            invariant
                0 <= i <= g.len(),
                g.len() == customers.len(),
                forall|j: int| 0 <= j < i ==> #[trigger] g[j] == 0i32,
                forall|j: int| i <= j < g.len() ==> g[j] == grumpy[j],
            decreases g.len() - i,
        {
            g.set(i, 0);
            i += 1;
        }
        (customers, g, minutes)
    } else if mutation_kind == 5 {
        // set all grumpy to 1
        let mut g = grumpy;
        let mut i: usize = 0;
        while i < g.len()
            invariant
                0 <= i <= g.len(),
                g.len() == customers.len(),
                forall|j: int| 0 <= j < i ==> #[trigger] g[j] == 1i32,
                forall|j: int| i <= j < g.len() ==> g[j] == grumpy[j],
            decreases g.len() - i,
        {
            g.set(i, 1);
            i += 1;
        }
        (customers, g, minutes)
    } else if mutation_kind == 6 {
        // set minutes to 1
        (customers, grumpy, 1i32)
    } else if mutation_kind == 7 {
        // set minutes to n (max window)
        let n = customers.len() as i32;
        (customers, grumpy, n)
    } else if mutation_kind == 8 {
        // set all customers to 0
        let mut c = customers;
        let mut i: usize = 0;
        while i < c.len()
            invariant
                0 <= i <= c.len(),
                c.len() == grumpy.len(),
                forall|j: int| 0 <= j < i ==> #[trigger] c[j] == 0i32,
                forall|j: int| i <= j < c.len() ==> c[j] == customers[j],
            decreases c.len() - i,
        {
            c.set(i, 0);
            i += 1;
        }
        (c, grumpy, minutes)
    } else if mutation_kind == 9 {
        // set all customers to 1000
        let mut c = customers;
        let mut i: usize = 0;
        while i < c.len()
            invariant
                0 <= i <= c.len(),
                c.len() == grumpy.len(),
                forall|j: int| 0 <= j < i ==> #[trigger] c[j] == 1000i32,
                forall|j: int| i <= j < c.len() ==> c[j] == customers[j],
            decreases c.len() - i,
        {
            c.set(i, 1000);
            i += 1;
        }
        (c, grumpy, minutes)
    } else {
        // fallback: identity
        (customers, grumpy, minutes)
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
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn mutate(customers: Vec<i32>, grumpy: Vec<i32>, minutes: i32, mk: u8) -> (Vec<i32>, Vec<i32>, i32) {
    generate_test_case(customers, grumpy, minutes, mk)
}

extern crate serde_json;
use serde_json::json;

fn random_customers(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(0, 1000) as i32);
    }
    v
}

fn random_grumpy(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(0, 1) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1052);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |customers: Vec<i32>, grumpy: Vec<i32>, minutes: i32,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}|{:?}|{}", customers, grumpy, minutes);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::max_satisfied(customers.clone(), grumpy.clone(), minutes);
        writeln!(out, "{}", json!({
            "input": {"customers": customers, "grumpy": grumpy, "minutes": minutes},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example 1 from description
    {
        let (c, g, m) = mutate(
            vec![1, 0, 1, 2, 1, 1, 7, 5],
            vec![0, 1, 0, 1, 0, 1, 0, 1],
            3,
            0,
        );
        emit(c, g, m, &mut seen, &mut out, &mut count);
    }
    // Example 2 from description
    {
        let (c, g, m) = mutate(vec![1], vec![0], 1, 0);
        emit(c, g, m, &mut seen, &mut out, &mut count);
    }

    // Seed inputs × mutations
    let seed_inputs: Vec<(Vec<i32>, Vec<i32>, i32)> = vec![
        (vec![1, 0, 1, 2, 1, 1, 7, 5], vec![0, 1, 0, 1, 0, 1, 0, 1], 3),
        (vec![1], vec![0], 1),
        (vec![0, 0, 0], vec![1, 1, 1], 2),
        (vec![1000, 1000, 1000], vec![1, 0, 1], 1),
        (vec![5, 10, 15, 20], vec![1, 1, 1, 1], 4),
        (vec![100, 200], vec![0, 0], 1),
        (vec![0], vec![1], 1),
        (vec![500, 500, 500, 500, 500], vec![0, 1, 0, 1, 0], 3),
    ];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    for (c, g, m) in &seed_inputs {
        for &mk in &mutation_kinds {
            let (rc, rg, rm) = mutate(c.clone(), g.clone(), *m, mk);
            emit(rc, rg, rm, &mut seen, &mut out, &mut count);
        }
    }

    // Random test cases with diverse sizes
    while count < target_count {
        let n = match count % 5 {
            0 => rng.gen_range_usize(1, 5),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 100),    // medium
            3 => rng.gen_range_usize(101, 1000),  // large
            _ => rng.gen_range_usize(1001, 5000), // very large
        };
        let m = rng.gen_range_usize(1, n) as i32;
        let c = random_customers(&mut rng, n);
        let g = random_grumpy(&mut rng, n);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let (rc, rg, rm) = mutate(c, g, m, mk);
        emit(rc, rg, rm, &mut seen, &mut out, &mut count);
    }
}
