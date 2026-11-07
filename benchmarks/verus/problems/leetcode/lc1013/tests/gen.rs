use vstd::prelude::*;

verus! {

pub fn generate_test_case(arr: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        3 <= arr.len() <= 50_000,
        forall|i: int| 0 <= i < arr.len() ==> -10_000 <= #[trigger] arr[i] <= 10_000,
    ensures
        3 <= result.len() <= 50_000,
        forall|i: int| 0 <= i < result.len() ==> -10_000 <= #[trigger] result[i] <= 10_000,
{
    if mutation_kind == 0 {
        // identity
        arr
    } else if mutation_kind == 1 {
        // set first element to 0
        let mut a = arr;
        a.set(0, 0);
        a
    } else if mutation_kind == 2 {
        // set last element to 0
        let mut a = arr;
        let last = a.len() - 1;
        a.set(last, 0);
        a
    } else if mutation_kind == 3 && arr.len() < 50_000 {
        // grow by one element (push 0)
        let mut a = arr;
        a.push(0);
        a
    } else if mutation_kind == 4 && arr.len() > 3 {
        // shrink by one element (pop)
        let mut a = arr;
        a.pop();
        a
    } else if mutation_kind == 5 {
        // negate first element
        let mut a = arr;
        let v = a[0];
        if v > -10_000 {
            a.set(0, -v);
        }
        a
    } else if mutation_kind == 6 {
        // set all elements to 0
        let mut a = arr;
        let mut i: usize = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                a.len() == arr.len(),
                3 <= a.len() <= 50_000,
                forall|j: int| 0 <= j < i ==> a[j] == 0,
                forall|j: int| i <= j < a.len() ==> a[j] == arr[j],
            decreases a.len() - i,
        {
            a.set(i, 0);
            i += 1;
        }
        a
    } else if mutation_kind == 7 {
        // nudge first element up (if < 10_000)
        let mut a = arr;
        if a[0] < 10_000 {
            a.set(0, a[0] + 1);
        }
        a
    } else if mutation_kind == 8 {
        // nudge first element down (if > -10_000)
        let mut a = arr;
        if a[0] > -10_000 {
            a.set(0, a[0] - 1);
        }
        a
    } else if mutation_kind == 9 {
        // set first element to boundary 10_000
        let mut a = arr;
        a.set(0, 10_000);
        a
    } else if mutation_kind == 10 {
        // set first element to boundary -10_000
        let mut a = arr;
        a.set(0, -10_000);
        a
    } else if mutation_kind == 11 && arr.len() >= 4 {
        // swap first two elements
        let mut a = arr;
        let v0 = a[0];
        let v1 = a[1];
        a.set(0, v1);
        a.set(1, v0);
        a
    } else {
        // fallback: identity
        arr
    }
}

} // verus!

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
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn mutate(arr: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(arr, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_arr(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut arr = Vec::with_capacity(len);
    for _ in 0..len {
        arr.push(rng.gen_range_i64(-10_000, 10_000) as i32);
    }
    arr
}

/// Build an array whose total sum is divisible by 3 (likely partitionable)
fn divisible_by_3_arr(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut arr = Vec::with_capacity(len);
    let mut sum: i64 = 0;
    for i in 0..len - 1 {
        let v = rng.gen_range_i64(-10_000, 10_000);
        arr.push(v as i32);
        sum += v;
    }
    // Adjust last element so sum % 3 == 0
    let rem = ((sum % 3) + 3) % 3;
    let last = -rem; // makes sum + last divisible by 3
    if last >= -10_000 && last <= 10_000 {
        arr.push(last as i32);
    } else {
        arr.push(0);
    }
    arr
}

/// Build an array that is guaranteed to partition into 3 equal parts
fn partitionable_arr(rng: &mut Rng, len: usize) -> Vec<i32> {
    assert!(len >= 3);
    // Split into 3 segments, each summing to target
    let target = rng.gen_range_i64(-3_000, 3_000);
    let seg1_len = 1.max(len / 3);
    let seg2_len = 1.max(len / 3);
    let seg3_len = len - seg1_len - seg2_len;

    let mut arr = Vec::with_capacity(len);

    // Build segment 1: random values, adjust last to hit target
    let mut sum: i64 = 0;
    for _ in 0..seg1_len - 1 {
        let v = rng.gen_range_i64(-5_000, 5_000);
        arr.push(v as i32);
        sum += v;
    }
    let adjust = target - sum;
    if adjust >= -10_000 && adjust <= 10_000 {
        arr.push(adjust as i32);
    } else {
        arr.push(0);
    }

    // Build segment 2
    sum = 0;
    for _ in 0..seg2_len - 1 {
        let v = rng.gen_range_i64(-5_000, 5_000);
        arr.push(v as i32);
        sum += v;
    }
    let adjust = target - sum;
    if adjust >= -10_000 && adjust <= 10_000 {
        arr.push(adjust as i32);
    } else {
        arr.push(0);
    }

    // Build segment 3
    sum = 0;
    for _ in 0..seg3_len - 1 {
        let v = rng.gen_range_i64(-5_000, 5_000);
        arr.push(v as i32);
        sum += v;
    }
    let adjust = target - sum;
    if adjust >= -10_000 && adjust <= 10_000 {
        arr.push(adjust as i32);
    } else {
        arr.push(0);
    }

    arr
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count_target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |arr: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= count_target { return; }
        let key = format!("{:?}", arr);
        if !seen.insert(key) { return; }
        let output = Solution::can_three_parts_equal_sum(arr.clone());
        writeln!(out, "{}", json!({"input": {"arr": arr}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![0, 2, 1, -6, 6, -7, 9, 1, 2, 0, 1],       // true
        vec![0, 2, 1, -6, 6, 7, 9, -1, 2, 0, 1],        // false
        vec![3, 3, 6, 5, -2, 2, 5, 1, -9, 4],            // true
    ];

    // Emit examples with identity mutation
    for ex in &examples {
        emit(mutate(ex.clone(), 0), &mut seen, &mut out, &mut count);
    }

    // Hand-crafted edge cases
    let edge_cases: Vec<Vec<i32>> = vec![
        vec![0, 0, 0],                        // minimal true
        vec![1, 1, 1],                         // true: each part = 1
        vec![1, 2, 3],                         // false: sum=6, but 1!=2!=3
        vec![0, 0, 0, 0],                      // true
        vec![10_000, 10_000, 10_000],           // true: boundary values
        vec![-10_000, -10_000, -10_000],        // true: negative boundary
        vec![1, -1, 1, -1, 1, -1],             // false
    ];

    for ec in &edge_cases {
        emit(mutate(ec.clone(), 0), &mut seen, &mut out, &mut count);
    }

    // Generate partitionable arrays (should return true) with diverse sizes
    let part_sizes = [3, 5, 10, 30, 100, 500, 1000, 5000, 10000];
    for &sz in &part_sizes {
        if count >= count_target { break; }
        let arr = partitionable_arr(&mut rng, sz);
        let mk = (rng.next_u64() % 12) as u8;
        emit(mutate(arr, mk), &mut seen, &mut out, &mut count);
    }

    // Generate random arrays with diverse size classes
    for i in 0..40 {
        if count >= count_target { break; }
        let n = match i % 6 {
            0 => rng.gen_range_usize(3, 5),           // tiny
            1 => rng.gen_range_usize(6, 20),          // small
            2 => rng.gen_range_usize(21, 100),         // medium
            3 => rng.gen_range_usize(101, 1000),       // large
            4 => rng.gen_range_usize(1001, 5000),      // big
            _ => rng.gen_range_usize(5001, 20000),     // very big
        };
        let arr = random_arr(&mut rng, n);
        let mk = (rng.next_u64() % 12) as u8;
        emit(mutate(arr, mk), &mut seen, &mut out, &mut count);
    }

    // Generate divisible-by-3 arrays (more likely to be true)
    for i in 0..25 {
        if count >= count_target { break; }
        let n = match i % 5 {
            0 => rng.gen_range_usize(3, 5),
            1 => rng.gen_range_usize(6, 30),
            2 => rng.gen_range_usize(31, 200),
            3 => rng.gen_range_usize(201, 2000),
            _ => rng.gen_range_usize(2001, 10000),
        };
        let arr = divisible_by_3_arr(&mut rng, n);
        let mk = (rng.next_u64() % 12) as u8;
        emit(mutate(arr, mk), &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random sizes and mutations
    while count < count_target {
        let n = rng.gen_range_usize(3, 5000);
        let use_partitionable = rng.next_u64() % 3 == 0;
        let arr = if use_partitionable {
            partitionable_arr(&mut rng, n)
        } else {
            random_arr(&mut rng, n)
        };
        let mk = (rng.next_u64() % 12) as u8;
        emit(mutate(arr, mk), &mut seen, &mut out, &mut count);
    }
}
