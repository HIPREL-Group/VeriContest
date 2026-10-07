use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_restaurants: Vec<Vec<i32>>,
    seed_vf: i32,
    seed_mp: i32,
    seed_md: i32,
    mutation_kind: u8,
) -> (result: (Vec<Vec<i32>>, i32, i32, i32))
    requires
        1 <= seed_restaurants.len() <= 10000,
        forall |i: int| #![trigger seed_restaurants[i]]
            0 <= i < seed_restaurants.len() ==>
            seed_restaurants[i].len() == 5
            && 1 <= seed_restaurants[i][0] <= 100000
            && 1 <= seed_restaurants[i][1] <= 100000
            && (seed_restaurants[i][2] == 0 || seed_restaurants[i][2] == 1)
            && 1 <= seed_restaurants[i][3] <= 100000
            && 1 <= seed_restaurants[i][4] <= 100000,
        seed_vf == 0 || seed_vf == 1,
        1 <= seed_mp <= 100000,
        1 <= seed_md <= 100000,
        forall |i: int, j: int|
            0 <= i < j < seed_restaurants.len()
            ==> seed_restaurants[i][0] != seed_restaurants[j][0],
    ensures
        1 <= result.0.len() <= 10000,
        forall |i: int| #![trigger result.0[i]]
            0 <= i < result.0.len() ==>
            result.0[i].len() == 5
            && 1 <= result.0[i][0] <= 100000
            && 1 <= result.0[i][1] <= 100000
            && (result.0[i][2] == 0 || result.0[i][2] == 1)
            && 1 <= result.0[i][3] <= 100000
            && 1 <= result.0[i][4] <= 100000,
        result.1 == 0 || result.1 == 1,
        1 <= result.2 <= 100000,
        1 <= result.3 <= 100000,
        forall |i: int, j: int|
            0 <= i < j < result.0.len()
            ==> result.0[i][0] != result.0[j][0],
{
    if mutation_kind == 0 {
        (seed_restaurants, seed_vf, seed_mp, seed_md)
    } else if mutation_kind == 1 {
        let new_vf = if seed_vf == 0 { 1i32 } else { 0i32 };
        (seed_restaurants, new_vf, seed_mp, seed_md)
    } else if mutation_kind == 2 {
        (seed_restaurants, seed_vf, 1, seed_md)
    } else if mutation_kind == 3 {
        (seed_restaurants, seed_vf, seed_mp, 1)
    } else if mutation_kind == 4 {
        (seed_restaurants, seed_vf, 100000, seed_md)
    } else if mutation_kind == 5 {
        (seed_restaurants, seed_vf, seed_mp, 100000)
    } else if mutation_kind == 6 {
        (seed_restaurants, seed_vf, 100000, 100000)
    } else if mutation_kind == 7 && seed_mp < 100000 {
        (seed_restaurants, seed_vf, seed_mp + 1, seed_md)
    } else if mutation_kind == 8 && seed_mp > 1 {
        (seed_restaurants, seed_vf, seed_mp - 1, seed_md)
    } else if mutation_kind == 9 && seed_md < 100000 {
        (seed_restaurants, seed_vf, seed_mp, seed_md + 1)
    } else if mutation_kind == 10 && seed_md > 1 {
        (seed_restaurants, seed_vf, seed_mp, seed_md - 1)
    } else if mutation_kind == 11 {
        let new_mp = seed_mp / 2;
        (seed_restaurants, seed_vf, if new_mp >= 1 { new_mp } else { 1 }, seed_md)
    } else if mutation_kind == 12 {
        let new_md = seed_md / 2;
        (seed_restaurants, seed_vf, seed_mp, if new_md >= 1 { new_md } else { 1 })
    } else {
        (seed_restaurants, seed_vf, seed_mp, seed_md)
    }
}

} // verus!

extern crate serde_json;
use serde_json::json;

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

fn random_restaurants(rng: &mut Rng, n: usize) -> Vec<Vec<i32>> {
    let mut restaurants = Vec::with_capacity(n);
    // Use sequential IDs shuffled to guarantee distinctness
    let mut ids: Vec<i32> = (1..=(n as i32)).collect();
    // Fisher-Yates shuffle
    for i in (1..n).rev() {
        let j = rng.gen_range_usize(0, i);
        ids.swap(i, j);
    }
    for i in 0..n {
        let id = ids[i];
        let rating = rng.gen_range_i64(1, 100000) as i32;
        let vegan = rng.gen_range_i64(0, 1) as i32;
        let price = rng.gen_range_i64(1, 100000) as i32;
        let distance = rng.gen_range_i64(1, 100000) as i32;
        restaurants.push(vec![id, rating, vegan, price, distance]);
    }
    restaurants
}

fn all_vegan_restaurants(rng: &mut Rng, n: usize) -> Vec<Vec<i32>> {
    let mut restaurants = Vec::with_capacity(n);
    for i in 0..n {
        let id = (i + 1) as i32;
        let rating = rng.gen_range_i64(1, 100000) as i32;
        let price = rng.gen_range_i64(1, 100000) as i32;
        let distance = rng.gen_range_i64(1, 100000) as i32;
        restaurants.push(vec![id, rating, 1, price, distance]);
    }
    restaurants
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1333);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |restaurants: Vec<Vec<i32>>,
                    vegan_friendly: i32,
                    max_price: i32,
                    max_distance: i32,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= target_count { return; }
        let key = format!("{:?}:{}:{}:{}", restaurants, vegan_friendly, max_price, max_distance);
        if !seen.insert(key) { return; }
        let output = Solution::filter_restaurants(restaurants.clone(), vegan_friendly, max_price, max_distance);
        writeln!(out, "{}", json!({
            "input": {
                "restaurants": restaurants,
                "veganFriendly": vegan_friendly,
                "maxPrice": max_price,
                "maxDistance": max_distance
            },
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example test cases from description.md
    let ex_restaurants = vec![
        vec![1, 4, 1, 40, 10],
        vec![2, 8, 0, 50, 5],
        vec![3, 8, 1, 30, 4],
        vec![4, 10, 0, 10, 3],
        vec![5, 1, 1, 15, 1],
    ];
    emit(ex_restaurants.clone(), 1, 50, 10, &mut seen, &mut out, &mut count);
    emit(ex_restaurants.clone(), 0, 50, 10, &mut seen, &mut out, &mut count);
    emit(ex_restaurants.clone(), 0, 30, 3, &mut seen, &mut out, &mut count);

    // Structured seed inputs with all mutation kinds
    let seed_inputs: Vec<(Vec<Vec<i32>>, i32, i32, i32)> = vec![
        // Single restaurant
        (vec![vec![1, 5, 1, 10, 10]], 1, 10, 10),
        (vec![vec![1, 5, 0, 10, 10]], 1, 10, 10),
        (vec![vec![1, 5, 1, 10, 10]], 0, 10, 10),
        // Two restaurants, same rating
        (vec![vec![1, 5, 1, 10, 10], vec![2, 5, 0, 20, 20]], 0, 50, 50),
        // Two restaurants, different rating
        (vec![vec![1, 3, 1, 10, 10], vec![2, 7, 0, 20, 20]], 0, 50, 50),
        // All vegan
        (vec![vec![1, 10, 1, 5, 5], vec![2, 20, 1, 15, 15], vec![3, 30, 1, 25, 25]], 1, 30, 30),
        // None vegan
        (vec![vec![1, 10, 0, 5, 5], vec![2, 20, 0, 15, 15]], 1, 30, 30),
        // Edge: max values
        (vec![vec![100000, 100000, 1, 100000, 100000]], 1, 100000, 100000),
        // Edge: min values
        (vec![vec![1, 1, 0, 1, 1]], 0, 1, 1),
    ];

    let mutation_kinds: Vec<u8> = (0..=13).collect();

    for (rest, vf, mp, md) in &seed_inputs {
        for &mk in &mutation_kinds {
            let (r, v, p, d) = generate_test_case(rest.clone(), *vf, *mp, *md, mk);
            emit(r.clone(), v, p, d, &mut seen, &mut out, &mut count);
        }
    }

    // Random inputs across size classes
    while count < target_count {
        let n = match count % 6 {
            0 => 1,
            1 => rng.gen_range_usize(1, 5),
            2 => rng.gen_range_usize(5, 20),
            3 => rng.gen_range_usize(20, 100),
            4 => rng.gen_range_usize(100, 500),
            _ => rng.gen_range_usize(500, 10000),
        };

        let restaurants = if count % 8 == 0 {
            all_vegan_restaurants(&mut rng, n)
        } else {
            random_restaurants(&mut rng, n)
        };

        let vegan_friendly = rng.gen_range_i64(0, 1) as i32;

        let max_price = match count % 5 {
            0 => 1,
            1 => 100000,
            2 => rng.gen_range_i64(1, 50000) as i32,
            3 => rng.gen_range_i64(50000, 100000) as i32,
            _ => rng.gen_range_i64(1, 100000) as i32,
        };

        let max_distance = match count % 4 {
            0 => 1,
            1 => 100000,
            2 => rng.gen_range_i64(1, 50000) as i32,
            _ => rng.gen_range_i64(1, 100000) as i32,
        };

        let mk = rng.gen_range_usize(0, 13) as u8;
        let (r, v, p, d) = generate_test_case(restaurants, vegan_friendly, max_price, max_distance, mk);
        emit(r, v, p, d, &mut seen, &mut out, &mut count);
    }
}
