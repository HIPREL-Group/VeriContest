use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n_param: i32,
    num_mines: i32,
    fixed_coord: i32,
    mutation_kind: u8,
) -> (result: (i32, Vec<Vec<i32>>))
    requires
        1 <= n_param <= 500,
        1 <= num_mines <= n_param,
        0 <= fixed_coord < n_param,
    ensures
        1 <= result.0 <= 500,
        1 <= result.1.len() <= 5000,
        forall|i: int| 0 <= i < result.1.len() ==> #[trigger] result.1[i].len() == 2,
        forall|i: int| 0 <= i < result.1.len() ==> 0 <= #[trigger] result.1[i][0] < result.0 && 0 <= result.1[i][1] < result.0,
        forall|i: int, j: int|
            0 <= i < j < result.1.len()
            ==> (result.1[i][0] != result.1[j][0] || result.1[i][1] != result.1[j][1]),
{
    let n = n_param;

    if mutation_kind == 1 {
        // Row placement: mine[k] = [fixed_coord, k]
        let row = fixed_coord;
        let mut mines: Vec<Vec<i32>> = Vec::new();
        let mut k: i32 = 0;
        while k < num_mines
            invariant
                0 <= k <= num_mines,
                num_mines <= n,
                1 <= n <= 500,
                0 <= row < n,
                mines@.len() == k as int,
                forall|idx: int| 0 <= idx < mines@.len() ==> (#[trigger] mines@[idx]).len() == 2,
                forall|idx: int| 0 <= idx < mines@.len() ==> (
                    mines@[idx][0] == row
                    && mines@[idx][1] == idx as i32
                ),
            decreases num_mines - k,
        {
            let mut pair: Vec<i32> = Vec::new();
            pair.push(row);
            pair.push(k);
            mines.push(pair);
            k = k + 1;
        }

        proof {
            assert forall|a: int, b: int| 0 <= a < b < mines@.len() implies (
                mines@[a][0] != mines@[b][0] || mines@[a][1] != mines@[b][1]
            ) by {
                assert(mines@[a][1] == a as i32);
                assert(mines@[b][1] == b as i32);
            }
        }

        (n, mines)
    } else if mutation_kind == 2 {
        // Diagonal placement: mine[k] = [k, k]
        let mut mines: Vec<Vec<i32>> = Vec::new();
        let mut k: i32 = 0;
        while k < num_mines
            invariant
                0 <= k <= num_mines,
                num_mines <= n,
                1 <= n <= 500,
                mines@.len() == k as int,
                forall|idx: int| 0 <= idx < mines@.len() ==> (#[trigger] mines@[idx]).len() == 2,
                forall|idx: int| 0 <= idx < mines@.len() ==> (
                    mines@[idx][0] == idx as i32
                    && mines@[idx][1] == idx as i32
                ),
            decreases num_mines - k,
        {
            let mut pair: Vec<i32> = Vec::new();
            pair.push(k);
            pair.push(k);
            mines.push(pair);
            k = k + 1;
        }

        proof {
            assert forall|a: int, b: int| 0 <= a < b < mines@.len() implies (
                mines@[a][0] != mines@[b][0] || mines@[a][1] != mines@[b][1]
            ) by {
                assert(mines@[a][0] == a as i32);
                assert(mines@[b][0] == b as i32);
            }
        }

        (n, mines)
    } else {
        // Column placement: mine[k] = [k, fixed_coord]
        let col = fixed_coord;
        let mut mines: Vec<Vec<i32>> = Vec::new();
        let mut k: i32 = 0;
        while k < num_mines
            invariant
                0 <= k <= num_mines,
                num_mines <= n,
                1 <= n <= 500,
                0 <= col < n,
                mines@.len() == k as int,
                forall|idx: int| 0 <= idx < mines@.len() ==> (#[trigger] mines@[idx]).len() == 2,
                forall|idx: int| 0 <= idx < mines@.len() ==> (
                    mines@[idx][0] == idx as i32
                    && mines@[idx][1] == col
                ),
            decreases num_mines - k,
        {
            let mut pair: Vec<i32> = Vec::new();
            pair.push(k);
            pair.push(col);
            mines.push(pair);
            k = k + 1;
        }

        proof {
            assert forall|a: int, b: int| 0 <= a < b < mines@.len() implies (
                mines@[a][0] != mines@[b][0] || mines@[a][1] != mines@[b][1]
            ) by {
                assert(mines@[a][0] == a as i32);
                assert(mines@[b][0] == b as i32);
            }
        }

        (n, mines)
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

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);

    use std::io::Write;

    // Example inputs from description.md
    let examples: Vec<(i32, Vec<Vec<i32>>)> = vec![
        (5, vec![vec![4, 2]]),
        (1, vec![vec![0, 0]]),
    ];

    for (n, mines) in &examples {
        let result = Solution::order_of_largest_plus_sign(*n, mines.clone());
        writeln!(out, "{}", json!({
            "input": {"n": n, "mines": mines},
            "output": result
        })).unwrap();
    }

    let mut generated = examples.len();

    while generated < count {
        // Size classes for n
        let n: i32 = match generated % 5 {
            0 => rng.gen_range_i64(1, 5) as i32,        // tiny
            1 => rng.gen_range_i64(1, 10) as i32,       // small
            2 => rng.gen_range_i64(10, 50) as i32,      // medium
            3 => rng.gen_range_i64(50, 200) as i32,     // large
            _ => rng.gen_range_i64(200, 500) as i32,    // max
        };

        let num_mines = rng.gen_range_i64(1, n as i64) as i32;
        let fixed_coord = rng.gen_range_i64(0, (n - 1) as i64) as i32;
        let mutation_kind = rng.gen_range_i64(0, 2) as u8;

        let (result_n, mines) = generate_test_case(n, num_mines, fixed_coord, mutation_kind);
        let result = Solution::order_of_largest_plus_sign(result_n, mines.clone());

        let mines_json: Vec<Vec<i32>> = mines.iter().map(|v| v.clone()).collect();
        writeln!(out, "{}", json!({
            "input": {"n": result_n, "mines": mines_json},
            "output": result
        })).unwrap();

        generated += 1;
    }
}
