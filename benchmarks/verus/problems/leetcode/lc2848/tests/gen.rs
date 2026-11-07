use vstd::prelude::*;

verus! {

spec fn valid_interval(pair: Vec<i32>) -> bool {
    pair.len() == 2 && 1 <= pair[0] <= pair[1] <= 100
}

pub fn generate_test_case(
    starts: &Vec<i32>,
    deltas: &Vec<i32>,
    mutation_kind: u8,
) -> (result: Vec<Vec<i32>>)
    requires
        1 <= starts.len() <= 100,
        starts.len() == deltas.len(),
        forall|i: int| 0 <= i < starts.len() ==> 1 <= #[trigger] starts[i] <= 100,
        forall|i: int| 0 <= i < deltas.len() ==> 0 <= #[trigger] deltas[i],
    ensures
        1 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> (#[trigger] result.deep_view()[i]).len() == 2,
        forall|i: int| 0 <= i < result.len() ==> 1 <= (#[trigger] result.deep_view()[i])[0] <= result.deep_view()[i][1] <= 100,
{
    let n = starts.len();
    let mut result: Vec<Vec<i32>> = Vec::new();
    let mut k: usize = 0;

    while k < n
        invariant
            0 <= k <= n,
            n == starts.len(),
            n == deltas.len(),
            1 <= n <= 100,
            result.len() == k,
            forall|i: int| 0 <= i < starts.len() ==> 1 <= #[trigger] starts[i] <= 100,
            forall|i: int| 0 <= i < deltas.len() ==> 0 <= #[trigger] deltas[i],
            forall|j: int| 0 <= j < k ==> valid_interval(#[trigger] result[j]),
        decreases n - k,
    {
        let s: i32;
        let e: i32;

        if mutation_kind == 1 {
            s = 1;
            e = 100;
        } else if mutation_kind == 2 {
            s = starts[k];
            e = starts[k];
        } else if mutation_kind == 3 && k == 0 && starts[0] < 100 {
            s = starts[k] + 1;
            let d = deltas[k];
            e = if d <= 100 - s { s + d } else { 100 };
        } else if mutation_kind == 4 && k == 0 && starts[0] > 1 {
            s = starts[k] - 1;
            let d = deltas[k];
            e = if d <= 100 - s { s + d } else { 100 };
        } else if mutation_kind == 5 {
            s = 1;
            e = 1;
        } else if mutation_kind == 6 {
            s = 100;
            e = 100;
        } else if mutation_kind == 7 {
            s = 50;
            e = 50;
        } else {
            s = starts[k];
            let d = deltas[k];
            e = if d <= 100 - s { s + d } else { 100 };
        }

        let mut pair: Vec<i32> = Vec::new();
        pair.push(s);
        pair.push(e);

        proof {
            assert(pair.len() == 2);
            assert(pair[0] == s);
            assert(pair[1] == e);
            assert(1 <= s && s <= e && e <= 100);
            assert(valid_interval(pair));
        }

        result.push(pair);
        k = k + 1;
    }

    proof {
        assert forall|i: int| 0 <= i < result.len() implies #[trigger] result[i].len() == 2 by {
            assert(valid_interval(result[i]));
        };
        assert forall|i: int| 0 <= i < result.len()
            implies 1 <= result[i][0] <= #[trigger] result[i][1] <= 100 by {
            assert(valid_interval(result[i]));
            assert(result[i].len() == 2);
        };
    }

    result
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

fn random_starts_and_deltas(rng: &mut Rng, len: usize) -> (Vec<i32>, Vec<i32>) {
    let mut starts = Vec::with_capacity(len);
    let mut deltas = Vec::with_capacity(len);
    for _ in 0..len {
        starts.push(rng.gen_range_i64(1, 100) as i32);
        deltas.push(rng.gen_range_i64(0, 99) as i32);
    }
    (starts, deltas)
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2848);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<Vec<i32>>,
                    seen: &mut HashSet<Vec<Vec<i32>>>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= goal { return; }
        if !seen.insert(nums.clone()) { return; }
        let output = Solution::number_of_points(nums.clone());
        writeln!(out, "{}", json!({
            "input": {"nums": nums},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example inputs from description
    let examples: Vec<Vec<Vec<i32>>> = vec![
        vec![vec![3, 6], vec![1, 5], vec![4, 7]],
        vec![vec![1, 3], vec![5, 8]],
    ];
    for ex in examples {
        emit(ex, &mut seen, &mut out, &mut count);
    }

    // Interesting seed configurations x all mutation kinds
    let seeds: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![1], vec![0]),
        (vec![1], vec![99]),
        (vec![100], vec![0]),
        (vec![50], vec![0]),
        (vec![1, 50, 100], vec![10, 10, 0]),
        (vec![1, 1, 1], vec![99, 99, 99]),
        (vec![1, 2, 3, 4, 5], vec![0, 0, 0, 0, 0]),
        (vec![10, 20, 30], vec![5, 5, 5]),
        (vec![1, 5, 10], vec![4, 4, 90]),
        (vec![50, 50, 50], vec![0, 0, 0]),
    ];

    for (starts, deltas) in &seeds {
        for mk in 0..=7u8 {
            if count >= goal { break; }
            let nums = generate_test_case(starts, deltas, mk);
            emit(nums, &mut seen, &mut out, &mut count);
        }
        if count >= goal { break; }
    }

    // Random test cases with diverse size classes
    while count < goal {
        let n = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 50),
            3 => rng.gen_range_usize(51, 100),
            _ => 100,
        };
        let (starts, deltas) = random_starts_and_deltas(&mut rng, n);
        let mk = rng.gen_range_usize(0, 7) as u8;
        let nums = generate_test_case(&starts, &deltas, mk);
        emit(nums, &mut seen, &mut out, &mut count);
    }

    eprintln!("Generated {} test cases", count);
}
