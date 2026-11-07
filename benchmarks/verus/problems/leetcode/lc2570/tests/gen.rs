use vstd::prelude::*;

verus! {

pub fn construct_rows(raw: Vec<Vec<i32>>) -> (result: Vec<Vec<i32>>)
    ensures
        1 <= result.len() <= 200,
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == 2,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i][0] <= 1000 && 1 <= result[i][1] <= 1000,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> #[trigger] result[i][0] < #[trigger] result[j][0],
{
    let count = if raw.len() == 0 { 1usize } else if raw.len() > 200 { 200usize } else { raw.len() };
    let mut result: Vec<Vec<i32>> = Vec::new();
    let mut i = 0usize;
    let mut previous = 0i32;
    while i < count
        invariant
            1 <= count <= 200, 0 <= i <= count, result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> #[trigger] result[j].len() == 2,
            forall|j: int| 0 <= j < result.len() ==> 1 <= #[trigger] result[j][0] <= 1000 && 1 <= result[j][1] <= 1000,
            0 <= previous <= 1000 - count as int + i as int,
            i > 0 ==> result[i - 1][0] == previous,
            forall|j: int, k: int| 0 <= j < k < result.len() ==> #[trigger] result[j][0] < #[trigger] result[k][0],
        decreases count - i,
    {
        let a = if i < raw.len() && raw[i].len() > 0 { raw[i][0] } else { 1 };
        let b = if i < raw.len() && raw[i].len() > 1 { raw[i][1] } else { 1 };
        let mut a = if a < 1 { 1 } else if a > 1000 { 1000 } else { a };
        let mut b = if b < 1 { 1 } else if b > 1000 { 1000 } else { b };
        let upper = 1000 - count as i32 + i as i32 + 1;
        let v = a;
        let v = if v > upper { upper } else { v };
        let v = if v <= previous { previous + 1 } else { v };
        a = v;
        assert forall|j: int| 0 <= j < result.len() implies result[j][0] < v by {
            if j < i - 1 { assert(result[j][0] < result[(i - 1) as int][0]); }
        }
        previous = v;
        let mut row = Vec::new();
        row.push(a);
        row.push(b);
        result.push(row);
        i += 1;
    }
    result
}

pub fn generate_test_case(nums1: Vec<Vec<i32>>, nums2: Vec<Vec<i32>>) -> (result: (Vec<Vec<i32>>, Vec<Vec<i32>>))
    ensures
        1 <= result.0.len() <= 200,
        forall|i: int| 0 <= i < result.0.len() ==> #[trigger] result.0[i].len() == 2,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i][0] <= 1000 && 1 <= result.0[i][1] <= 1000,
        forall|i: int, j: int| 0 <= i < j < result.0.len() ==> #[trigger] result.0[i][0] < #[trigger] result.0[j][0],
        1 <= result.1.len() <= 200,
        forall|i: int| 0 <= i < result.1.len() ==> #[trigger] result.1[i].len() == 2,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i][0] <= 1000 && 1 <= result.1[i][1] <= 1000,
        forall|i: int, j: int| 0 <= i < j < result.1.len() ==> #[trigger] result.1[i][0] < #[trigger] result.1[j][0],
{
    (construct_rows(nums1), construct_rows(nums2))
}


fn build_array(ids: &Vec<i32>, vals: &Vec<i32>, mutation_kind: u8) -> (result: Vec<Vec<i32>>)
    requires
        ids.len() == vals.len(),
        1 <= ids.len() <= 200,
        forall|i: int| 0 <= i < ids.len() ==> 1 <= #[trigger] ids[i] <= 1000,
        forall|i: int| 0 <= i < vals.len() ==> 1 <= #[trigger] vals[i] <= 1000,
    ensures
        result.len() == ids.len(),
        1 <= result.len() <= 200,
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == 2,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i][0] <= 1000 && 1 <= result[i][1] <= 1000,
{
    let mut result: Vec<Vec<i32>> = Vec::new();
    let mut idx: usize = 0;
    while idx < ids.len()
        invariant
            ids.len() == vals.len(),
            1 <= ids.len() <= 200,
            0 <= idx <= ids.len(),
            result.len() == idx,
            forall|j: int| 0 <= j < idx as int ==> (#[trigger] result[j]).len() == 2,
            forall|j: int| 0 <= j < idx as int ==> 1 <= (#[trigger] result[j])[0] <= 1000
                && 1 <= result[j][1] <= 1000,
            forall|i: int| 0 <= i < ids.len() ==> 1 <= #[trigger] ids[i] <= 1000,
            forall|i: int| 0 <= i < vals.len() ==> 1 <= #[trigger] vals[i] <= 1000,
        decreases ids.len() - idx,
    {
        let id_val: i32 = if mutation_kind == 1 {
            1i32
        } else if mutation_kind == 2 {
            1000i32
        } else {
            ids[idx]
        };
        let val_val: i32 = if mutation_kind == 3 {
            1i32
        } else if mutation_kind == 4 {
            1000i32
        } else {
            vals[idx]
        };

        let mut pair: Vec<i32> = Vec::new();
        pair.push(id_val);
        pair.push(val_val);
        assert(pair.len() == 2);
        assert(pair[0] == id_val);
        assert(pair[1] == val_val);
        assert(1 <= id_val <= 1000);
        assert(1 <= val_val <= 1000);
        result.push(pair);
        idx += 1;
    }
    result
}

pub fn generate_candidate(
    ids1: &Vec<i32>,
    vals1: &Vec<i32>,
    ids2: &Vec<i32>,
    vals2: &Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<Vec<i32>>, Vec<Vec<i32>>))
    requires
        ids1.len() == vals1.len(),
        1 <= ids1.len() <= 200,
        ids2.len() == vals2.len(),
        1 <= ids2.len() <= 200,
        forall|i: int| 0 <= i < ids1.len() ==> 1 <= #[trigger] ids1[i] <= 1000,
        forall|i: int| 0 <= i < vals1.len() ==> 1 <= #[trigger] vals1[i] <= 1000,
        forall|i: int| 0 <= i < ids2.len() ==> 1 <= #[trigger] ids2[i] <= 1000,
        forall|i: int| 0 <= i < vals2.len() ==> 1 <= #[trigger] vals2[i] <= 1000,
    ensures
        1 <= result.0.len() <= 200,
        1 <= result.1.len() <= 200,
        forall|i: int| 0 <= i < result.0.len() ==> #[trigger] result.0[i].len() == 2,
        forall|i: int| 0 <= i < result.1.len() ==> #[trigger] result.1[i].len() == 2,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i][0] <= 1000 && 1 <= result.0[i][1] <= 1000,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i][0] <= 1000 && 1 <= result.1[i][1] <= 1000,
{
    if mutation_kind == 5 {
        // swap roles
        let n1 = build_array(ids2, vals2, 0);
        let n2 = build_array(ids1, vals1, 0);
        (n1, n2)
    } else {
        let n1 = build_array(ids1, vals1, mutation_kind);
        let n2 = build_array(ids2, vals2, 0);
        (n1, n2)
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

fn random_id_val_arrays(rng: &mut Rng, len: usize) -> (Vec<i32>, Vec<i32>) {
    let mut ids = Vec::with_capacity(len);
    let mut vals = Vec::with_capacity(len);
    for _ in 0..len {
        ids.push(rng.gen_range_i64(1, 1000) as i32);
        vals.push(rng.gen_range_i64(1, 1000) as i32);
    }
    (ids, vals)
}

fn main() {
    use std::io::Write;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);

    let mut rng = Rng::new(seed);

    // Example inputs from the problem description
    let examples: Vec<(Vec<Vec<i32>>, Vec<Vec<i32>>)> = vec![
        (vec![vec![1,2],vec![2,3],vec![4,5]], vec![vec![1,4],vec![3,2],vec![4,1]]),
        (vec![vec![2,4],vec![3,6],vec![5,5]], vec![vec![1,3],vec![4,3]]),
    ];

    let mut generated = 0usize;

    // Write example test cases first
    for (nums1, nums2) in &examples {
        if generated >= count { break; }
        let (nums1, nums2) = generate_test_case(nums1.clone(), nums2.clone());
        let result = Solution::merge_arrays(nums1.clone(), nums2.clone());
        writeln!(out, "{}", json!({
            "input": {"nums1": nums1, "nums2": nums2},
            "output": result
        })).unwrap();
        generated += 1;
    }

    // Generate random test cases
    while generated < count {
        // Size classes for array lengths
        let n1: usize = match generated % 5 {
            0 => rng.gen_range_usize(1, 3),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 50),     // medium
            3 => rng.gen_range_usize(51, 150),    // large
            _ => rng.gen_range_usize(150, 200),   // max
        };
        let n2: usize = match (generated / 5) % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 50),
            3 => rng.gen_range_usize(51, 150),
            _ => rng.gen_range_usize(150, 200),
        };

        let (ids1, vals1) = random_id_val_arrays(&mut rng, n1);
        let (ids2, vals2) = random_id_val_arrays(&mut rng, n2);

        // Cycle through mutation kinds 0..=5
        let mutation_kind = (generated % 6) as u8;

        let (nums1, nums2) = generate_candidate(&ids1, &vals1, &ids2, &vals2, mutation_kind);
        let (nums1, nums2) = generate_test_case(nums1.clone(), nums2.clone());
        let result = Solution::merge_arrays(nums1.clone(), nums2.clone());

        writeln!(out, "{}", json!({
            "input": {"nums1": nums1, "nums2": nums2},
            "output": result
        })).unwrap();

        generated += 1;
    }

    eprintln!("Generated {} test cases to {}", generated, out_path.display());
}
