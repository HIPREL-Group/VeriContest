use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    gas: Vec<i32>,
    cost: Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= gas.len() <= 100_000,
        gas.len() == cost.len(),
        forall|i: int| 0 <= i < gas.len() ==> 0 <= #[trigger] gas[i] <= 10_000,
        forall|i: int| 0 <= i < cost.len() ==> 0 <= #[trigger] cost[i] <= 10_000,
    ensures
        result.0.len() == result.1.len(),
        1 <= result.0.len() <= 100_000,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 10_000,
        forall|i: int| 0 <= i < result.1.len() ==> 0 <= #[trigger] result.1[i] <= 10_000,
{
    if mutation_kind == 0 {
        // identity
        (gas, cost)
    } else if mutation_kind == 1 {
        // set all gas to 0
        let mut g = gas;
        let mut i: usize = 0;
        while i < g.len()
            invariant
                0 <= i <= g.len(),
                g.len() == gas.len(),
                forall|j: int| 0 <= j < i ==> g[j] == 0,
                forall|j: int| i <= j < g.len() ==> g[j] == gas[j],
            decreases g.len() - i,
        {
            g.set(i, 0);
            i += 1;
        }
        (g, cost)
    } else if mutation_kind == 2 {
        // set all cost to 0 (always completable)
        let mut c = cost;
        let mut i: usize = 0;
        while i < c.len()
            invariant
                0 <= i <= c.len(),
                c.len() == cost.len(),
                forall|j: int| 0 <= j < i ==> c[j] == 0,
                forall|j: int| i <= j < c.len() ==> c[j] == cost[j],
            decreases c.len() - i,
        {
            c.set(i, 0);
            i += 1;
        }
        (gas, c)
    } else if mutation_kind == 3 {
        // set all gas and cost to same value
        let mut g = gas;
        let mut c = cost;
        let mut i: usize = 0;
        while i < g.len()
            invariant
                0 <= i <= g.len(),
                g.len() == gas.len(),
                c.len() == cost.len(),
                gas.len() == cost.len(),
                forall|j: int| 0 <= j < i ==> g[j] == 5000,
                forall|j: int| i <= j < g.len() ==> g[j] == gas[j],
                forall|j: int| 0 <= j < i ==> c[j] == 5000,
                forall|j: int| i <= j < c.len() ==> c[j] == cost[j],
            decreases g.len() - i,
        {
            g.set(i, 5000);
            c.set(i, 5000);
            i += 1;
        }
        (g, c)
    } else if mutation_kind == 4 {
        // nudge first gas element up (cap at 10000)
        let mut g = gas;
        if g[0] < 10_000 {
            g.set(0, g[0] + 1);
        }
        (g, cost)
    } else if mutation_kind == 5 {
        // nudge first cost element down (floor at 0)
        let mut c = cost;
        if c[0] > 0 {
            c.set(0, c[0] - 1);
        }
        (gas, c)
    } else if mutation_kind == 6 {
        // set first gas to max, first cost to 0
        let mut g = gas;
        let mut c = cost;
        g.set(0, 10_000);
        c.set(0, 0);
        (g, c)
    } else if mutation_kind == 7 {
        // swap gas and cost arrays
        (cost, gas)
    } else if mutation_kind == 8 && gas.len() < 100_000 && cost.len() < 100_000 {
        // grow: append one element
        let mut g = gas;
        let mut c = cost;
        g.push(0);
        c.push(0);
        (g, c)
    } else if mutation_kind == 9 && gas.len() > 1 && cost.len() > 1 {
        // shrink: remove last element
        let mut g = gas;
        let mut c = cost;
        g.pop();
        c.pop();
        (g, c)
    } else {
        // fallback: identity
        (gas, cost)
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

fn gen_call(gas: Vec<i32>, cost: Vec<i32>, mutation_kind: u8) -> (Vec<i32>, Vec<i32>) {
    generate_test_case(gas, cost, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_vec(rng: &mut Rng, len: usize, lo: i32, hi: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(lo as i64, hi as i64) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let mut rng = Rng::new(134);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let target = 100;

    let mut emit = |gas: Vec<i32>, cost: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?},{:?}", gas, cost);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::can_complete_circuit(gas.clone(), cost.clone());
        writeln!(out, "{}", json!({"input": {"gas": gas, "cost": cost}, "output": output})).unwrap();
        *count += 1;
    };

    // Hand-crafted seeds
    let seeds: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![1, 2, 3, 4, 5], vec![3, 4, 5, 1, 2]),
        (vec![2, 3, 4], vec![3, 4, 3]),
        (vec![5], vec![4]),
        (vec![4], vec![5]),
        (vec![0], vec![0]),
        (vec![10000], vec![10000]),
        (vec![0, 0, 0], vec![0, 0, 0]),
        (vec![3, 1, 1], vec![1, 1, 3]),
        (vec![1, 1, 3], vec![3, 1, 1]),
        (vec![10000, 0, 0], vec![0, 0, 10000]),
        (vec![0, 0, 10000], vec![10000, 0, 0]),
        (vec![1, 2], vec![2, 1]),
        (vec![5, 8, 2, 8], vec![6, 5, 6, 6]),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Apply every mutation to every seed
    for (g, c) in &seeds {
        for &mk in &mutation_kinds {
            let (rg, rc) = gen_call(g.clone(), c.clone(), mk);
            emit(rg, rc, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations, varying sizes
    for i in 0..200 {
        if count >= target { break; }
        let n = match i % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 10000),
        };
        let gas = random_vec(&mut rng, n, 0, 10_000);
        let cost = random_vec(&mut rng, n, 0, 10_000);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let (rg, rc) = gen_call(gas, cost, mk);
        emit(rg, rc, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with identity mutation
    while count < target {
        let n = rng.gen_range_usize(1, 100);
        let gas = random_vec(&mut rng, n, 0, 10_000);
        let cost = random_vec(&mut rng, n, 0, 10_000);
        let (rg, rc) = gen_call(gas, cost, 0);
        emit(rg, rc, &mut seen, &mut out, &mut count);
    }
}
