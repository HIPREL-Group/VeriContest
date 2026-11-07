use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    water_amounts: &Vec<i32>,
    capacity: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= water_amounts.len() <= 1000,
        1 <= capacity <= 1_000_000_000,
        forall|j: int| 0 <= j < water_amounts.len() ==> 1 <= #[trigger] water_amounts[j] <= 1_000_000,
        forall|j: int| 0 <= j < water_amounts.len() ==> #[trigger] water_amounts[j] <= capacity,
    ensures
        1 <= result.0.len() <= 1000,
        1 <= result.1 <= 1000000000,
        forall|j: int| 0 <= j < result.0.len() ==> 1 <= #[trigger] result.0[j] <= 1000000,
        forall|j: int| 0 <= j < result.0.len() ==> #[trigger] result.0[j] <= result.1,
{
    if mutation_kind == 0 {
        let plants = water_amounts.clone();
        (plants, capacity)
    } else if mutation_kind == 1 && water_amounts.len() < 1000 {
        let mut plants = water_amounts.clone();
        let v = plants[0];
        plants.push(v);
        (plants, capacity)
    } else if mutation_kind == 2 && water_amounts.len() > 1 {
        let mut plants = water_amounts.clone();
        plants.pop();
        (plants, capacity)
    } else if mutation_kind == 3 {
        let mut plants: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < water_amounts.len()
            invariant
                0 <= i <= water_amounts.len(),
                plants.len() == i,
                1 <= water_amounts.len() <= 1000,
                1 <= capacity <= 1_000_000_000,
                forall|k: int| 0 <= k < i ==> #[trigger] plants[k] == 1i32,
            decreases water_amounts.len() - i,
        {
            plants.push(1);
            i += 1;
        }
        (plants, capacity)
    } else if mutation_kind == 4 {
        if capacity <= 1_000_000 {
            let mut plants: Vec<i32> = Vec::new();
            let mut i: usize = 0;
            while i < water_amounts.len()
                invariant
                    0 <= i <= water_amounts.len(),
                    plants.len() == i,
                    1 <= water_amounts.len() <= 1000,
                    1 <= capacity <= 1_000_000,
                    forall|k: int| 0 <= k < i ==> #[trigger] plants[k] == capacity,
                decreases water_amounts.len() - i,
            {
                plants.push(capacity);
                i += 1;
            }
            (plants, capacity)
        } else {
            let plants = water_amounts.clone();
            (plants, capacity)
        }
    } else if mutation_kind == 5 {
        let mut plants = water_amounts.clone();
        plants.set(0, 1);
        (plants, capacity)
    } else if mutation_kind == 6 {
        let mut plants = water_amounts.clone();
        let last = plants.len() - 1;
        let v = plants[last];
        if v < 1_000_000 && v < capacity {
            let new_v = if capacity < 1_000_000 {
                if v + 1 <= capacity { (v + 1) as i32 } else { v }
            } else {
                (v + 1) as i32
            };
            plants.set(last, new_v);
        }
        (plants, capacity)
    } else if mutation_kind == 7 {
        let mut plants = water_amounts.clone();
        let last = plants.len() - 1;
        let v = plants[last];
        if v > 1 {
            plants.set(last, v - 1);
        }
        (plants, capacity)
    } else if mutation_kind == 8 && water_amounts.len() >= 2 {
        let mut plants = water_amounts.clone();
        let last = plants.len() - 1;
        let first_val = plants[0];
        let last_val = plants[last];
        plants.set(0, last_val);
        plants.set(last, first_val);
        (plants, capacity)
    } else if mutation_kind == 9 {
        let mut max_val: i32 = water_amounts[0];
        let mut i: usize = 1;
        while i < water_amounts.len()
            invariant
                1 <= i <= water_amounts.len(),
                1 <= water_amounts.len() <= 1000,
                forall|j: int| 0 <= j < water_amounts.len() ==> 1 <= #[trigger] water_amounts[j] <= 1_000_000,
                1 <= max_val <= 1_000_000,
                forall|j: int| 0 <= j < i ==> #[trigger] water_amounts[j] <= max_val,
                exists|j: int| 0 <= j < i && water_amounts[j] == max_val,
            decreases water_amounts.len() - i,
        {
            if water_amounts[i] > max_val {
                max_val = water_amounts[i];
            }
            i += 1;
        }
        let plants = water_amounts.clone();
        (plants, max_val)
    } else {
        let plants = water_amounts.clone();
        (plants, capacity)
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

fn random_plants(rng: &mut Rng, len: usize, cap: i32) -> Vec<i32> {
    let max_val = cap.min(1_000_000) as i64;
    let mut plants = Vec::with_capacity(len);
    for _ in 0..len {
        plants.push(rng.gen_range_i64(1, max_val) as i32);
    }
    plants
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let mut rng = Rng::new(2079);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let target = 100;

    let mut emit = |plants: Vec<i32>, capacity: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}_{}", plants, capacity);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::watering_plants(plants.clone(), capacity);
        writeln!(out, "{}", json!({"input": {"plants": plants, "capacity": capacity}, "output": output})).unwrap();
        *count += 1;
    };

    // Example test case from description.md
    emit(vec![2, 2, 3, 3], 5, &mut seen, &mut out, &mut count);

    // Seed pool: interesting configurations
    let seed_configs: Vec<(Vec<i32>, i32)> = vec![
        (vec![1], 1),
        (vec![1], 1_000_000_000),
        (vec![1_000_000], 1_000_000),
        (vec![1, 1, 1], 1),
        (vec![1, 2, 3, 4, 5], 5),
        (vec![5, 5, 5, 5, 5], 5),
        (vec![3, 3, 3], 10),
        (vec![1, 2, 4, 8], 8),
        (vec![10, 10, 10], 10),
        (vec![1, 1000000], 1000000),
    ];

    // Emit all seed configs with all mutation kinds
    for (plants, cap) in &seed_configs {
        for mk in 0..=10u8 {
            let (rp, rc) = generate_test_case(plants, *cap, mk);
            emit(rp, rc, &mut seen, &mut out, &mut count);
            if count >= target { break; }
        }
        if count >= target { break; }
    }

    // Random test cases with diverse sizes and mutations
    while count < target {
        let n = match count % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 500),
            _ => rng.gen_range_usize(501, 1000),
        };

        let cap_kind = count % 4;
        let base_cap: i32 = match cap_kind {
            0 => 1_000_000,
            1 => rng.gen_range_i64(1, 1_000_000) as i32,
            2 => rng.gen_range_i64(1, 1_000_000_000) as i32,
            _ => 1_000_000_000,
        };

        let plants = random_plants(&mut rng, n, base_cap);
        let mk = (rng.next_u64() % 11) as u8;
        let (result_plants, result_cap) = generate_test_case(&plants, base_cap, mk);
        emit(result_plants, result_cap, &mut seen, &mut out, &mut count);
    }

    eprintln!("Generated {} test cases", count);
}
