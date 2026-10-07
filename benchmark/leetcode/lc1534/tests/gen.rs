use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    len: usize,
    fill_val: i32,
    alt_val: i32,
    a: i32,
    b: i32,
    c: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32, i32, i32))
    requires
        3 <= len <= 100,
        0 <= fill_val <= 1000,
        0 <= alt_val <= 1000,
        0 <= a <= 1000,
        0 <= b <= 1000,
        0 <= c <= 1000,
    ensures
        3 <= result.0.len() <= 100,
        forall |i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 1000,
        0 <= result.1 <= 1000,
        0 <= result.2 <= 1000,
        0 <= result.3 <= 1000,
{
    let mut arr: Vec<i32> = Vec::new();
    let mut idx: usize = 0;

    // Build array based on mutation_kind
    if mutation_kind == 0 {
        // All same value
        while idx < len
            invariant
                0 <= idx <= len,
                3 <= len <= 100,
                0 <= fill_val <= 1000,
                arr.len() == idx,
                forall |j: int| 0 <= j < idx ==> #[trigger] arr[j] == fill_val,
                forall |j: int| 0 <= j < idx ==> 0 <= #[trigger] arr[j] <= 1000,
            decreases len - idx,
        {
            arr.push(fill_val);
            idx += 1;
        }
    } else if mutation_kind == 1 {
        // All same except first element uses alt_val
        arr.push(alt_val);
        idx = 1;
        while idx < len
            invariant
                1 <= idx <= len,
                3 <= len <= 100,
                0 <= fill_val <= 1000,
                0 <= alt_val <= 1000,
                arr.len() == idx,
                0 <= arr[0int] <= 1000,
                forall |j: int| 1 <= j < idx ==> #[trigger] arr[j] == fill_val,
                forall |j: int| 0 <= j < idx ==> 0 <= #[trigger] arr[j] <= 1000,
            decreases len - idx,
        {
            arr.push(fill_val);
            idx += 1;
        }
    } else if mutation_kind == 2 {
        // All same except last element uses alt_val
        while idx < len - 1
            invariant
                0 <= idx <= len - 1,
                3 <= len <= 100,
                0 <= fill_val <= 1000,
                arr.len() == idx,
                forall |j: int| 0 <= j < idx ==> #[trigger] arr[j] == fill_val,
                forall |j: int| 0 <= j < idx ==> 0 <= #[trigger] arr[j] <= 1000,
            decreases (len - 1) - idx,
        {
            arr.push(fill_val);
            idx += 1;
        }
        arr.push(alt_val);
    } else if mutation_kind == 3 {
        // All zeros
        while idx < len
            invariant
                0 <= idx <= len,
                3 <= len <= 100,
                arr.len() == idx,
                forall |j: int| 0 <= j < idx ==> #[trigger] arr[j] == 0i32,
                forall |j: int| 0 <= j < idx ==> 0 <= #[trigger] arr[j] <= 1000,
            decreases len - idx,
        {
            arr.push(0i32);
            idx += 1;
        }
    } else if mutation_kind == 4 {
        // All max (1000)
        while idx < len
            invariant
                0 <= idx <= len,
                3 <= len <= 100,
                arr.len() == idx,
                forall |j: int| 0 <= j < idx ==> #[trigger] arr[j] == 1000i32,
                forall |j: int| 0 <= j < idx ==> 0 <= #[trigger] arr[j] <= 1000,
            decreases len - idx,
        {
            arr.push(1000i32);
            idx += 1;
        }
    } else if mutation_kind == 5 {
        // Alternating fill_val and alt_val
        while idx < len
            invariant
                0 <= idx <= len,
                3 <= len <= 100,
                0 <= fill_val <= 1000,
                0 <= alt_val <= 1000,
                arr.len() == idx,
                forall |j: int| 0 <= j < idx ==> 0 <= #[trigger] arr[j] <= 1000,
            decreases len - idx,
        {
            if idx % 2 == 0 {
                arr.push(fill_val);
            } else {
                arr.push(alt_val);
            }
            idx += 1;
        }
    } else if mutation_kind == 6 && fill_val < 1000 {
        // Nudge fill_val up by 1
        let nudged = fill_val + 1;
        while idx < len
            invariant
                0 <= idx <= len,
                3 <= len <= 100,
                0 < nudged <= 1000,
                arr.len() == idx,
                forall |j: int| 0 <= j < idx ==> #[trigger] arr[j] == nudged,
                forall |j: int| 0 <= j < idx ==> 0 <= #[trigger] arr[j] <= 1000,
            decreases len - idx,
        {
            arr.push(nudged);
            idx += 1;
        }
    } else if mutation_kind == 7 && fill_val > 0 {
        // Nudge fill_val down by 1
        let nudged = fill_val - 1;
        while idx < len
            invariant
                0 <= idx <= len,
                3 <= len <= 100,
                0 <= nudged < 1000,
                arr.len() == idx,
                forall |j: int| 0 <= j < idx ==> #[trigger] arr[j] == nudged,
                forall |j: int| 0 <= j < idx ==> 0 <= #[trigger] arr[j] <= 1000,
            decreases len - idx,
        {
            arr.push(nudged);
            idx += 1;
        }
    } else {
        // Fallback: all fill_val
        while idx < len
            invariant
                0 <= idx <= len,
                3 <= len <= 100,
                0 <= fill_val <= 1000,
                arr.len() == idx,
                forall |j: int| 0 <= j < idx ==> #[trigger] arr[j] == fill_val,
                forall |j: int| 0 <= j < idx ==> 0 <= #[trigger] arr[j] <= 1000,
            decreases len - idx,
        {
            arr.push(fill_val);
            idx += 1;
        }
    };

    // Apply mutations to a, b, c
    let out_a: i32 = if mutation_kind == 8 { 0i32 }
        else if mutation_kind == 9 { 1000i32 }
        else { a };
    let out_b: i32 = if mutation_kind == 8 { 0i32 }
        else if mutation_kind == 9 { 1000i32 }
        else { b };
    let out_c: i32 = if mutation_kind == 8 { 0i32 }
        else if mutation_kind == 9 { 1000i32 }
        else { c };

    (arr, out_a, out_b, out_c)
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

fn random_arr(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut arr = Vec::with_capacity(len);
    for _ in 0..len {
        arr.push(rng.gen_range_i64(0, 1000) as i32);
    }
    arr
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1534);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |arr: Vec<i32>, a: i32, b: i32, c: i32,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= target { return; }
        let key = format!("{:?}|{}|{}|{}", arr, a, b, c);
        if !seen.insert(key) { return; }
        let output = Solution::count_good_triplets(arr.clone(), a, b, c);
        writeln!(out, "{}", json!({
            "input": {"arr": arr, "a": a, "b": b, "c": c},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    emit(vec![3, 0, 1, 1, 9, 7], 7, 2, 3, &mut seen, &mut out, &mut count);
    emit(vec![1, 1, 2, 2, 3], 0, 0, 1, &mut seen, &mut out, &mut count);

    // Generated inputs with verified generator + mutations
    let fill_vals: Vec<i32> = vec![0, 500, 1000, 1, 999, 100, 42];
    let alt_vals: Vec<i32> = vec![0, 1000, 1, 500, 999];
    let abc_vals: Vec<i32> = vec![0, 1, 500, 999, 1000];
    let sizes: Vec<usize> = vec![3, 4, 5, 10, 20, 50, 100];
    let mutation_kinds: Vec<u8> = (0..=9).collect();

    for &sz in &sizes {
        for &fv in &fill_vals {
            for &mk in &mutation_kinds {
                if count >= target { break; }
                let av = alt_vals[mk as usize % alt_vals.len()];
                let a_val = abc_vals[mk as usize % abc_vals.len()];
                let b_val = abc_vals[(mk as usize + 1) % abc_vals.len()];
                let c_val = abc_vals[(mk as usize + 2) % abc_vals.len()];
                let (arr, out_a, out_b, out_c) = generate_test_case(sz, fv, av, a_val, b_val, c_val, mk);
                emit(arr, out_a, out_b, out_c, &mut seen, &mut out, &mut count);
            }
        }
    }

    // Random inputs for extra diversity
    while count < target {
        let len = match rng.gen_range_usize(0, 4) {
            0 => 3,
            1 => rng.gen_range_usize(3, 10),
            2 => rng.gen_range_usize(10, 50),
            3 => rng.gen_range_usize(50, 100),
            _ => 100,
        };
        let arr = random_arr(&mut rng, len);
        let a = rng.gen_range_i64(0, 1000) as i32;
        let b = rng.gen_range_i64(0, 1000) as i32;
        let c = rng.gen_range_i64(0, 1000) as i32;
        emit(arr, a, b, c, &mut seen, &mut out, &mut count);
    }
}
