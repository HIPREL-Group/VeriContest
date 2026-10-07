use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 100000,
        forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] == 0 || nums[i] == 1,
        exists|i: int| 0 <= i < nums.len() && nums[i] == 1,
    ensures
        1 <= result.len() <= 100000,
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] == 0 || result[i] == 1,
        exists|i: int| 0 <= i < result.len() && result[i] == 1,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set first element to 1
        let mut d = nums;
        d.set(0, 1);
        proof {
            assert(d[0int] == 1);
        }
        d
    } else if mutation_kind == 2 {
        // set last element to 1
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1);
        proof {
            assert(d[last as int] == 1);
        }
        d
    } else if mutation_kind == 3 {
        // set all elements to 1
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 100000,
                forall|j: int| 0 <= j < i ==> d[j] == 1,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        proof {
            assert(d[0int] == 1);
        }
        d
    } else if mutation_kind == 4 && nums.len() < 100000 {
        // grow by pushing 1
        let mut d = nums;
        d.push(1);
        proof {
            assert(d[d.len() as int - 1] == 1);
        }
        d
    } else if mutation_kind == 5 {
        // set all to 0 then set first to 1 (sparse: exactly one 1)
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 100000,
                forall|j: int| 0 <= j < i ==> d[j] == 0,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 0);
            i += 1;
        }
        d.set(0, 1);
        proof {
            assert(d[0int] == 1);
            assert forall|j: int| 0 <= j < d.len() implies #[trigger] d[j] == 0 || d[j] == 1 by {
                if j == 0 {
                    assert(d[0int] == 1);
                }
            }
        }
        d
    } else if mutation_kind == 6 {
        // set first to 0 and last to 1
        let mut d = nums;
        d.set(0, 0);
        let last = d.len() - 1;
        d.set(last, 1);
        proof {
            assert(d[last as int] == 1);
        }
        d
    } else if mutation_kind == 7 && nums.len() < 100000 {
        // grow by pushing 0 — original 1s still present
        let ghost witness = choose|i: int| 0 <= i < nums.len() && nums[i] == 1;
        let mut d = nums;
        d.push(0);
        proof {
            assert(0 <= witness < d.len() as int && d[witness] == 1);
        }
        d
    } else {
        // fallback: identity
        nums
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

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn mutate(nums: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(nums, mutation_kind)
}

fn random_binary_array(rng: &mut Rng, len: usize, min_ones: usize) -> Vec<i32> {
    let mut arr = Vec::with_capacity(len);
    let mut ones = 0usize;
    for i in 0..len {
        let val = if i == len - 1 && ones == 0 {
            1 // guarantee at least one 1
        } else if rng.gen_range_usize(0, 1) == 1 {
            1
        } else {
            0
        };
        if val == 1 { ones += 1; }
        arr.push(val);
    }
    // If we haven't reached min_ones, set trailing elements to 1
    let mut idx = len;
    while ones < min_ones && idx > 0 {
        idx -= 1;
        if arr[idx] == 0 {
            arr[idx] = 1;
            ones += 1;
        }
    }
    arr
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2134);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, total: &mut usize| {
        if *total >= count { return; }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let output = Solution::min_swaps(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *total += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![0,1,0,1,1,0,0],
        vec![0,1,1,1,0,0,1,1,0],
        vec![1,1,0,0,1],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];

    // Emit examples with all mutations
    for ex in &examples {
        for &mk in &mutation_kinds {
            let result = mutate(ex.clone(), mk);
            emit(result, &mut seen, &mut out, &mut total);
        }
    }

    // Hand-crafted interesting seeds
    let seeds: Vec<Vec<i32>> = vec![
        vec![1],                           // single element
        vec![1, 0],                        // minimal with both values
        vec![0, 1],                        // reversed
        vec![1, 1, 1, 1, 1],              // all 1s
        vec![1, 0, 0, 0, 0],              // one 1, rest 0s
        vec![0, 0, 0, 0, 1],              // 1 at end
        vec![1, 0, 1, 0, 1, 0, 1, 0],    // alternating
        vec![0, 0, 1, 1, 0, 0, 1, 1],    // grouped pairs
        vec![1, 1, 1, 0, 0, 0],          // grouped block
    ];

    for seed in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed.clone(), mk);
            emit(result, &mut seen, &mut out, &mut total);
        }
    }

    // Random arrays with diverse sizes and mutations
    while total < count {
        let n: usize = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),         // tiny
            1 => rng.gen_range_usize(1, 10),         // small
            2 => rng.gen_range_usize(11, 100),       // medium
            3 => rng.gen_range_usize(101, 1000),     // large
            _ => rng.gen_range_usize(1001, 100000),  // max
        };
        let min_ones = rng.gen_range_usize(1, n.max(1));
        let arr = random_binary_array(&mut rng, n, min_ones);
        let mk = rng.gen_range_usize(0, 7) as u8;
        let result = mutate(arr, mk);
        emit(result, &mut seen, &mut out, &mut total);
    }
}
