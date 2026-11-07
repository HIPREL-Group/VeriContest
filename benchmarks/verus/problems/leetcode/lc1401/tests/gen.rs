use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_radius: i32,
    seed_x_center: i32,
    seed_y_center: i32,
    seed_x1: i32,
    seed_y1: i32,
    // delta > 0 so that x2 = x1 + delta_x > x1, y2 = y1 + delta_y > y1
    delta_x: i32,
    delta_y: i32,
    mutation_kind: u8,
) -> (res: (i32, i32, i32, i32, i32, i32, i32))
    requires
        1 <= seed_radius <= 2000,
        -10_000 <= seed_x_center <= 10_000,
        -10_000 <= seed_y_center <= 10_000,
        -10_000 <= seed_x1 <= 9_999,
        -10_000 <= seed_y1 <= 9_999,
        1 <= delta_x <= 20_000,
        1 <= delta_y <= 20_000,
        seed_x1 as int + delta_x as int <= 10_000,
        seed_y1 as int + delta_y as int <= 10_000,
    ensures
        1 <= res.0 <= 2000,
        -10_000 <= res.1 <= 10_000,
        -10_000 <= res.2 <= 10_000,
        -10_000 <= res.3 <= 10_000,
        -10_000 <= res.4 <= 10_000,
        -10_000 <= res.5 <= 10_000,
        -10_000 <= res.6 <= 10_000,
        res.3 < res.5,
        res.4 < res.6,
{
    let x2 = seed_x1 + delta_x;
    let y2 = seed_y1 + delta_y;

    // Start with identity
    let mut radius = seed_radius;
    let mut x_center = seed_x_center;
    let mut y_center = seed_y_center;
    let mut x1 = seed_x1;
    let mut y1 = seed_y1;
    let mut out_x2 = x2;
    let mut out_y2 = y2;

    if mutation_kind == 1 && seed_radius < 2000 {
        // nudge radius up
        radius = seed_radius + 1;
    } else if mutation_kind == 2 && seed_radius > 1 {
        // nudge radius down
        radius = seed_radius - 1;
    } else if mutation_kind == 3 {
        // min radius
        radius = 1;
    } else if mutation_kind == 4 {
        // max radius
        radius = 2000;
    } else if mutation_kind == 5 && seed_radius <= 1000 {
        // double radius
        radius = seed_radius * 2;
    } else if mutation_kind == 6 {
        // halve radius (at least 1)
        let h = seed_radius / 2;
        radius = if h >= 1 { h } else { 1 };
    } else if mutation_kind == 7 {
        // center at origin
        x_center = 0;
        y_center = 0;
    } else if mutation_kind == 8 {
        // center at rectangle corner (x1, y1)
        x_center = seed_x1;
        y_center = seed_y1;
    } else if mutation_kind == 9 {
        // center at rectangle corner (x2, y2)
        x_center = x2;
        y_center = y2;
    } else if mutation_kind == 10 {
        // nudge x_center up
        if seed_x_center < 10_000 {
            x_center = seed_x_center + 1;
        }
    } else if mutation_kind == 11 {
        // nudge y_center up
        if seed_y_center < 10_000 {
            y_center = seed_y_center + 1;
        }
    } else if mutation_kind == 12 {
        // set rectangle to unit square at origin
        x1 = 0;
        y1 = 0;
        out_x2 = 1;
        out_y2 = 1;
    } else if mutation_kind == 13 {
        // set rectangle to max extents
        x1 = -10_000;
        y1 = -10_000;
        out_x2 = 10_000;
        out_y2 = 10_000;
    } else if mutation_kind == 14 {
        // negate x_center
        if seed_x_center > -10_000 && seed_x_center < 10_000 {
            x_center = -seed_x_center;
        }
    } else if mutation_kind == 15 {
        // negate y_center
        if seed_y_center > -10_000 && seed_y_center < 10_000 {
            y_center = -seed_y_center;
        }
    }
    // else: identity (mutation_kind == 0 or fallback)

    (radius, x_center, y_center, x1, y1, out_x2, out_y2)
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
    let mut generated = 0;
    let num_mutations: u8 = 16;

    // Example inputs from description.md
    let examples: Vec<(i32, i32, i32, i32, i32, i32, i32)> = vec![
        (1, 0, 0, 1, -1, 3, 1),
        (1, 1, 1, 1, -3, 2, -1),
        (1, 0, 0, -1, 0, 0, 1),
    ];

    // Emit examples first
    for &(radius, xc, yc, x1, y1, x2, y2) in &examples {
        let result = Solution::check_overlap(radius, xc, yc, x1, y1, x2, y2);
        let key = (radius, xc, yc, x1, y1, x2, y2);
        if seen.insert(key) {
            writeln!(out, "{}", json!({
                "input": {
                    "radius": radius,
                    "xCenter": xc,
                    "yCenter": yc,
                    "x1": x1,
                    "y1": y1,
                    "x2": x2,
                    "y2": y2,
                },
                "output": result,
            })).unwrap();
            generated += 1;
        }
    }

    // Interesting seed values for radius
    let radii: Vec<i32> = vec![1, 2, 10, 100, 500, 1000, 2000];
    // Interesting center values
    let centers: Vec<i32> = vec![-10000, -100, -1, 0, 1, 100, 10000];

    while generated < count {
        // Sample construction parameters
        let seed_radius = if generated % 5 == 0 {
            radii[rng.gen_range_usize(0, radii.len() - 1)]
        } else {
            rng.gen_range_i64(1, 2000) as i32
        };

        let seed_x_center = if generated % 5 == 0 {
            centers[rng.gen_range_usize(0, centers.len() - 1)]
        } else {
            rng.gen_range_i64(-10000, 10000) as i32
        };

        let seed_y_center = if generated % 5 == 0 {
            centers[rng.gen_range_usize(0, centers.len() - 1)]
        } else {
            rng.gen_range_i64(-10000, 10000) as i32
        };

        // x1 in [-10000, 9999] so there's room for x2 > x1
        let seed_x1 = rng.gen_range_i64(-10000, 9999) as i32;
        let seed_y1 = rng.gen_range_i64(-10000, 9999) as i32;

        let max_dx = 10000 - seed_x1;
        let max_dy = 10000 - seed_y1;

        let delta_x = rng.gen_range_i64(1, max_dx as i64) as i32;
        let delta_y = rng.gen_range_i64(1, max_dy as i64) as i32;

        let mutation = (generated as u8) % num_mutations;

        let (radius, xc, yc, x1, y1, x2, y2) = generate_test_case(
            seed_radius, seed_x_center, seed_y_center,
            seed_x1, seed_y1, delta_x, delta_y, mutation,
        );

        let key = (radius, xc, yc, x1, y1, x2, y2);
        if !seen.insert(key) {
            continue;
        }

        let result = Solution::check_overlap(radius, xc, yc, x1, y1, x2, y2);
        writeln!(out, "{}", json!({
            "input": {
                "radius": radius,
                "xCenter": xc,
                "yCenter": yc,
                "x1": x1,
                "y1": y1,
                "x2": x2,
                "y2": y2,
            },
            "output": result,
        })).unwrap();
        generated += 1;
    }

    eprintln!("Generated {} test cases to {:?}", generated, out_path);
}
