use vstd::prelude::*;

verus! {

pub fn generate_test_case(stones: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        2 <= stones.len() <= 1000,
        forall|i: int| 0 <= i < stones.len() ==> 1 <= #[trigger] stones[i] <= 1000,
    ensures
        2 <= result.len() <= 1000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1000,
{
    if mutation_kind == 0 {
        stones
    } else if mutation_kind == 1 {
        let mut s = stones;
        let last = s.len() - 1;
        s.set(last, 1);
        s
    } else if mutation_kind == 2 {
        let mut s = stones;
        let last = s.len() - 1;
        s.set(last, 1000);
        s
    } else if mutation_kind == 3 {
        let mut s = stones;
        let mut i: usize = 0;
        while i < s.len()
            invariant
                0 <= i <= s.len(),
                s.len() == stones.len(),
                2 <= s.len() <= 1000,
                forall|j: int| 0 <= j < i ==> s[j] == 1i32,
                forall|j: int| i <= j < s.len() ==> s[j] == stones[j],
            decreases
                s.len() - i,
        {
            s.set(i, 1);
            i += 1;
        }
        s
    } else if mutation_kind == 4 {
        let mut s = stones;
        let mut i: usize = 0;
        while i < s.len()
            invariant
                0 <= i <= s.len(),
                s.len() == stones.len(),
                2 <= s.len() <= 1000,
                forall|j: int| 0 <= j < i ==> s[j] == 1000i32,
                forall|j: int| i <= j < s.len() ==> s[j] == stones[j],
            decreases
                s.len() - i,
        {
            s.set(i, 1000);
            i += 1;
        }
        s
    } else if mutation_kind == 5 && stones.len() < 1000 {
        let mut s = stones;
        s.push(500);
        s
    } else if mutation_kind == 6 && stones.len() > 2 {
        let mut s = stones;
        s.pop();
        s
    } else if mutation_kind == 7 {
        let mut s = stones;
        if s[0] < 1000 {
            s.set(0, s[0] + 1);
        }
        s
    } else if mutation_kind == 8 {
        let mut s = stones;
        if s[0] > 1 {
            s.set(0, s[0] - 1);
        }
        s
    } else if mutation_kind == 9 && stones.len() >= 2 {
        let mut s = stones;
        let a = s[0];
        let b = s[1];
        s.set(0, b);
        s.set(1, a);
        s
    } else {
        stones
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

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    use std::io::Write;

    let mut rng = Rng::new(seed);
    let mut generated = 0usize;

    // Example 1
    {
        let stones = vec![5, 3, 1, 4, 2];
        let result = Solution::stone_game_vii(stones.clone());
        writeln!(out, "{}", json!({"input": {"stones": stones}, "output": result})).unwrap();
        generated += 1;
    }

    // Example 2
    {
        let stones = vec![7, 90, 5, 1, 100, 10, 10, 2];
        let result = Solution::stone_game_vii(stones.clone());
        writeln!(out, "{}", json!({"input": {"stones": stones}, "output": result})).unwrap();
        generated += 1;
    }

    let num_mutations: u8 = 10;

    while generated < count {
        let n: usize = match generated % 5 {
            0 => rng.gen_range_usize(2, 5),
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 500),
            _ => rng.gen_range_usize(501, 1000),
        };

        let mut stones: Vec<i32> = Vec::new();
        for _ in 0..n {
            let val = if generated % 5 == 0 {
                match rng.gen_range_usize(0, 4) {
                    0 => 1,
                    1 => 1000,
                    2 => 500,
                    3 => 1,
                    _ => 1000,
                }
            } else {
                rng.gen_range_i64(1, 1000) as i32
            };
            stones.push(val);
        }

        let mutation = (rng.next_u64() % num_mutations as u64) as u8;
        let test_stones = generate_test_case(stones, mutation);

        let result = Solution::stone_game_vii(test_stones.clone());
        writeln!(out, "{}", json!({"input": {"stones": test_stones}, "output": result})).unwrap();
        generated += 1;
    }

    eprintln!("Generated {} test cases to {:?}", generated, out_path);
}
