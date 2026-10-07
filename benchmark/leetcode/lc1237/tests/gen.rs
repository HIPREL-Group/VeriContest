use vstd::prelude::*;

verus! {

pub struct CustomFunction {
    pub values: Vec<Vec<i32>>,
}

pub open spec fn grid_val(f: Seq<Vec<i32>>, x: int, y: int) -> i32 {
    f[x]@[y]
}

pub open spec fn is_monotonic_grid(f: Seq<Vec<i32>>) -> bool {
    &&& f.len() >= 1001
    &&& forall |x: int| 0 <= x <= 1000 ==> (#[trigger] f[x])@.len() >= 1001
    &&& forall |x: int, y: int| 1 <= x < 1000 && 1 <= y <= 1000 ==>
        (#[trigger] grid_val(f, x, y)) < grid_val(f, x + 1, y)
    &&& forall |x: int, y: int| 1 <= x <= 1000 && 1 <= y < 1000 ==>
        (#[trigger] grid_val(f, x, y)) < grid_val(f, x, y + 1)
}

pub fn generate_test_case(cf: CustomFunction, z_seed: i32, mutation_kind: u8) -> (result: (CustomFunction, i32))
    requires
        is_monotonic_grid(cf.values@),
        1 <= z_seed <= 100,
    ensures
        is_monotonic_grid(result.0.values@),
        1 <= result.1 <= 100,
{
    let z = if mutation_kind == 0 {
        z_seed
    } else if mutation_kind == 1 && z_seed < 100 {
        z_seed + 1
    } else if mutation_kind == 2 && z_seed > 1 {
        z_seed - 1
    } else if mutation_kind == 3 {
        1i32
    } else if mutation_kind == 4 {
        100i32
    } else if mutation_kind == 5 {
        50i32
    } else if mutation_kind == 6 && z_seed <= 50 {
        z_seed * 2
    } else if mutation_kind == 7 {
        (z_seed - 1) / 2 + 1
    } else if mutation_kind == 8 {
        if z_seed <= 10 { z_seed * 10 } else { z_seed }
    } else {
        z_seed
    };

    (cf, z)
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
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }
    fn gen_u8(&mut self) -> u8 {
        (self.next_u64() % 256) as u8
    }
}

fn build_grid_unverified(formula: &str) -> Vec<Vec<i32>> {
    let mut values = Vec::with_capacity(1001);
    for x in 0..=1000usize {
        let mut row = Vec::with_capacity(1001);
        for y in 0..=1000usize {
            let val = match formula {
                "x*y" => (x as i64 * y as i64) as i32,
                "x+2*y" => (x + 2 * y) as i32,
                _ => (x + y) as i32,  // "x+y"
            };
            row.push(val);
        }
        values.push(row);
    }
    values
}

fn find_solution_unverified(values: &Vec<Vec<i32>>, z: i32) -> Vec<Vec<i32>> {
    let mut result: Vec<Vec<i32>> = Vec::new();
    let mut x: usize = 1;
    let mut y: usize = 1000;
    while x <= 1000 && y >= 1 {
        let val = values[x][y];
        if val == z {
            result.push(vec![x as i32, y as i32]);
            x += 1;
            if y == 0 { break; }
            y -= 1;
        } else if val < z {
            x += 1;
        } else {
            if y == 0 { break; }
            y -= 1;
        }
    }
    result
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
    let mut emitted = 0usize;

    // Build grids for different formulas
    let formulas = vec!["x+y", "x*y", "x+2*y"];
    let grids: Vec<Vec<Vec<i32>>> = formulas.iter().map(|f| build_grid_unverified(f)).collect();

    // Example test cases from description
    let examples: Vec<(usize, i32)> = vec![
        (0, 5),   // f=x+y, z=5 -> [[1,4],[2,3],[3,2],[4,1]]
        (1, 5),   // f=x*y, z=5 -> [[1,5],[5,1]]
    ];

    for (fi, z) in &examples {
        if emitted >= count { break; }
        let key = format!("{}_{}", fi, z);
        if seen.insert(key) {
            let output = find_solution_unverified(&grids[*fi], *z);
            writeln!(out, "{}", json!({
                "input": {"customfunction": formulas[*fi], "z": z},
                "output": output
            })).unwrap();
            emitted += 1;
        }
    }

    // Systematic z values with all formulas
    let z_values: Vec<i32> = vec![
        1, 2, 3, 4, 5, 10, 20, 25, 50, 75, 99, 100,
    ];

    for &z_seed in &z_values {
        for mk in 0..=9u8 {
            if emitted >= count { break; }
            let (_, z) = generate_test_case(
                CustomFunction { values: grids[0].clone() },
                z_seed,
                mk,
            );
            for (fi, grid) in grids.iter().enumerate() {
                if emitted >= count { break; }
                let key = format!("{}_{}", fi, z);
                if seen.insert(key) {
                    let output = find_solution_unverified(grid, z);
                    writeln!(out, "{}", json!({
                        "input": {"customfunction": formulas[fi], "z": z},
                        "output": output
                    })).unwrap();
                    emitted += 1;
                }
            }
        }
        if emitted >= count { break; }
    }

    // Fill remaining with random z values and mutations
    while emitted < count {
        let z_seed = rng.gen_range_i64(1, 100) as i32;
        let mk = rng.gen_u8() % 10;
        let (_, z) = generate_test_case(
            CustomFunction { values: grids[0].clone() },
            z_seed,
            mk,
        );
        let fi = (rng.next_u64() % formulas.len() as u64) as usize;
        let key = format!("{}_{}", fi, z);
        if seen.insert(key) {
            let output = find_solution_unverified(&grids[fi], z);
            writeln!(out, "{}", json!({
                "input": {"customfunction": formulas[fi], "z": z},
                "output": output
            })).unwrap();
            emitted += 1;
        }
    }
}
