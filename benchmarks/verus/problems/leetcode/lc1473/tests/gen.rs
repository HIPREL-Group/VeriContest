use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    houses: Vec<i32>,
    cost: Vec<Vec<i32>>,
    m: i32,
    n: i32,
    target: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<Vec<i32>>, i32, i32, i32))
    requires
        m as int == houses@.len(),
        m as int == cost@.len(),
        1 <= m <= 100,
        1 <= n <= 20,
        1 <= target <= m,
        forall|i: int| 0 <= i < m as int ==> 0 <= #[trigger] houses@[i] <= n,
        forall|i: int| 0 <= i < m as int ==> (#[trigger] cost@[i])@.len() == n as int,
        forall|i: int, j: int|
            0 <= i < m as int && 0 <= j < n as int ==> 1 <= #[trigger] cost@[i]@[j]
                <= 10_000,
    ensures
        result.2 as int == result.0@.len(),
        result.2 as int == result.1@.len(),
        1 <= result.2 <= 100,
        1 <= result.3 <= 20,
        1 <= result.4 <= result.2,
        forall|i: int| 0 <= i < result.2 as int ==> 0 <= #[trigger] result.0@[i] <= result.3,
        forall|i: int| 0 <= i < result.2 as int ==> (#[trigger] result.1@[i])@.len() == result.3 as int,
        forall|i: int, j: int|
            0 <= i < result.2 as int && 0 <= j < result.3 as int ==> 1 <= #[trigger] result.1@[i]@[j]
                <= 10_000,
{
    if mutation_kind == 0 {
        // identity
        (houses, cost, m, n, target)
    } else if mutation_kind == 1 {
        // set all houses to 0 (all unpainted)
        let mut new_houses: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < m as usize
            invariant
                0 <= i <= m as usize,
                1 <= m <= 100,
                1 <= n <= 20,
                new_houses.len() == i as nat,
                forall|k: int| 0 <= k < i as int ==> #[trigger] new_houses@[k] == 0,
            decreases m as usize - i,
        {
            new_houses.push(0i32);
            i += 1;
        }
        (new_houses, cost, m, n, target)
    } else if mutation_kind == 2 {
        // set all houses to color 1 (all pre-painted same color)
        let mut new_houses: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < m as usize
            invariant
                0 <= i <= m as usize,
                1 <= m <= 100,
                1 <= n <= 20,
                new_houses.len() == i as nat,
                forall|k: int| 0 <= k < i as int ==> #[trigger] new_houses@[k] == 1,
            decreases m as usize - i,
        {
            new_houses.push(1i32);
            i += 1;
        }
        (new_houses, cost, m, n, target)
    } else if mutation_kind == 3 {
        // set target to 1 (minimal neighborhoods)
        (houses, cost, m, n, 1i32)
    } else if mutation_kind == 4 {
        // set target to m (maximal neighborhoods)
        (houses, cost, m, n, m)
    } else {
        // fallback: identity
        (houses, cost, m, n, target)
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
}

struct Solution;
include!("../code.rs");

fn random_houses(rng: &mut Rng, m: usize, n: usize) -> Vec<i32> {
    let mut h = Vec::with_capacity(m);
    for _ in 0..m {
        h.push(rng.gen_range_i64(0, n as i64) as i32);
    }
    h
}

fn random_cost(rng: &mut Rng, m: usize, n: usize) -> Vec<Vec<i32>> {
    let mut c = Vec::with_capacity(m);
    for _ in 0..m {
        let mut row = Vec::with_capacity(n);
        for _ in 0..n {
            row.push(rng.gen_range_i64(1, 10_000) as i32);
        }
        c.push(row);
    }
    c
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1473);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |houses: Vec<i32>, cost: Vec<Vec<i32>>, m: i32, n: i32, target: i32,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= target_count { return; }
        let key = format!("{:?}:{:?}:{:?}:{:?}:{:?}", houses, cost, m, n, target);
        if !seen.insert(key) { return; }
        let output = Solution::min_cost(houses.clone(), cost.clone(), m, n, target);
        writeln!(out, "{}", json!({
            "input": {"houses": houses, "cost": cost, "m": m, "n": n, "target": target},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example 1: houses=[0,0,0,0,0], cost=[[1,10],[10,1],[10,1],[1,10],[5,1]], m=5, n=2, target=3
    let (h, c, m, n, t) = generate_test_case(
        vec![0,0,0,0,0],
        vec![vec![1,10],vec![10,1],vec![10,1],vec![1,10],vec![5,1]],
        5, 2, 3, 0,
    );
    emit(h, c, m, n, t, &mut seen, &mut out, &mut count);

    // Example 2: houses=[0,2,1,2,0], cost=[[1,10],[10,1],[10,1],[1,10],[5,1]], m=5, n=2, target=3
    let (h, c, m, n, t) = generate_test_case(
        vec![0,2,1,2,0],
        vec![vec![1,10],vec![10,1],vec![10,1],vec![1,10],vec![5,1]],
        5, 2, 3, 0,
    );
    emit(h, c, m, n, t, &mut seen, &mut out, &mut count);

    // Example 3: houses=[3,1,2,3], cost=[[1,1,1],[1,1,1],[1,1,1],[1,1,1]], m=4, n=3, target=3
    let (h, c, m, n, t) = generate_test_case(
        vec![3,1,2,3],
        vec![vec![1,1,1],vec![1,1,1],vec![1,1,1],vec![1,1,1]],
        4, 3, 3, 0,
    );
    emit(h, c, m, n, t, &mut seen, &mut out, &mut count);

    // Structured seeds with all mutation kinds
    let seed_inputs: Vec<(Vec<i32>, Vec<Vec<i32>>, i32, i32, i32)> = vec![
        // Single house
        (vec![0], vec![vec![5]], 1, 1, 1),
        (vec![1], vec![vec![5]], 1, 1, 1),
        // Two houses, 2 colors
        (vec![0, 0], vec![vec![1, 2], vec![3, 4]], 2, 2, 1),
        (vec![0, 0], vec![vec![1, 2], vec![3, 4]], 2, 2, 2),
        (vec![1, 0], vec![vec![1, 2], vec![3, 4]], 2, 2, 1),
        // All same pre-painted
        (vec![1, 1, 1], vec![vec![1, 2], vec![3, 4], vec![5, 6]], 3, 2, 1),
        // All different pre-painted
        (vec![1, 2, 1], vec![vec![1, 2], vec![3, 4], vec![5, 6]], 3, 2, 3),
        // All unpainted, 3 colors
        (vec![0, 0, 0], vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]], 3, 3, 2),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4];

    for (houses, cost, m, n, target) in &seed_inputs {
        for &mk in &mutation_kinds {
            let (h, c, mv, nv, tv) = generate_test_case(
                houses.clone(), cost.clone(), *m, *n, *target, mk,
            );
            emit(h, c, mv, nv, tv, &mut seen, &mut out, &mut count);
        }
    }

    // Random test cases across size classes
    while count < target_count {
        let m_val: usize = match count % 6 {
            0 => 1,                                           // minimal
            1 => rng.gen_range_usize(1, 3),                   // tiny
            2 => rng.gen_range_usize(2, 10),                  // small
            3 => rng.gen_range_usize(10, 30),                 // medium
            4 => rng.gen_range_usize(30, 70),                 // large
            _ => rng.gen_range_usize(70, 100),                // max
        };
        let n_val: usize = match count % 4 {
            0 => 1,
            1 => rng.gen_range_usize(1, 5),
            2 => rng.gen_range_usize(5, 12),
            _ => rng.gen_range_usize(12, 20),
        };
        let t_val: usize = rng.gen_range_usize(1, m_val);

        let houses = random_houses(&mut rng, m_val, n_val);
        let cost = random_cost(&mut rng, m_val, n_val);

        let mk = rng.gen_range_usize(0, 4) as u8;
        let (h, c, mv, nv, tv) = generate_test_case(
            houses, cost, m_val as i32, n_val as i32, t_val as i32, mk,
        );
        emit(h, c, mv, nv, tv, &mut seen, &mut out, &mut count);
    }
}
