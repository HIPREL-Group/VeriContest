use vstd::prelude::*;

verus! {

/// Total number of elements across all rows.
pub open spec fn total_len(nums: Seq<Vec<i32>>, i: int) -> int
    decreases nums.len() - i,
{
    if i >= nums.len() { 0 }
    else { nums[i].len() + total_len(nums, i + 1) }
}

proof fn total_len_nonneg(nums: Seq<Vec<i32>>, i: int)
    requires 0 <= i <= nums.len(),
    ensures total_len(nums, i) >= 0,
    decreases nums.len() - i,
{
    if i < nums.len() {
        total_len_nonneg(nums, i + 1);
    }
}

/// Constraints from the problem spec:
///   1 <= nums.len() <= 100_000
///   1 <= nums[i].len() <= 100_000  for all i
///   1 <= nums[i][j] <= 100_000     for all i, j
pub fn generate_test_case(nums: Vec<Vec<i32>>, mutation_kind: u8) -> (result: Vec<Vec<i32>>)
    requires
        1 <= nums@.len() <= 100_000,
        forall|i: int| 0 <= i < nums@.len() ==>
            1 <= (#[trigger] nums@[i]).len() <= 100_000,
        forall|i: int, j: int| 0 <= i < nums@.len() && 0 <= j < nums@[i].len() ==>
            1 <= (#[trigger] nums@[i][j]) <= 100_000,
    ensures
        1 <= result@.len() <= 100000,
        forall |i: int| 0 <= i < result@.len() ==>
            1 <= (#[trigger] result@[i]).len() <= 100000,
        forall |i: int, j: int| 0 <= i < result@.len() && 0 <= j < result@[i].len() ==>
            1 <= (#[trigger] result@[i][j]) <= 100000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set first element of first row to 1
        let mut n = nums;
        let mut row0 = n[0].clone();
        row0.set(0, 1i32);
        n.set(0, row0);
        n
    } else if mutation_kind == 2 {
        // set first element of first row to 100_000
        let mut n = nums;
        let mut row0 = n[0].clone();
        row0.set(0, 100_000i32);
        n.set(0, row0);
        n
    } else if mutation_kind == 3 {
        // set last element of last row to 1
        let mut n = nums;
        let last_r = n.len() - 1;
        let mut row = n[last_r].clone();
        let last_c = row.len() - 1;
        row.set(last_c, 1i32);
        n.set(last_r, row);
        n
    } else if mutation_kind == 4 {
        // set last element of last row to 100_000
        let mut n = nums;
        let last_r = n.len() - 1;
        let mut row = n[last_r].clone();
        let last_c = row.len() - 1;
        row.set(last_c, 100_000i32);
        n.set(last_r, row);
        n
    } else if mutation_kind == 5 && nums.len() < 100_000 {
        // grow: duplicate first row at end
        let mut n = nums;
        let row_copy = n[0].clone();
        n.push(row_copy);
        n
    } else if mutation_kind == 6 && nums.len() > 1 {
        // shrink: remove last row
        let mut n = nums;
        n.pop();
        n
    } else if mutation_kind == 7 {
        // set all elements in first row to 1
        let mut n = nums;
        let mut row = n[0].clone();
        let mut j: usize = 0;
        while j < row.len()
            invariant
                0 <= j <= row.len(),
                row.len() == nums@[0].len(),
                1 <= row.len() <= 100_000,
                forall|k: int| 0 <= k < j ==> row[k] == 1i32,
                forall|k: int| j <= k < row.len() ==> row[k] == nums@[0][k],
            decreases row.len() - j,
        {
            row.set(j, 1i32);
            j = j + 1;
        }
        n.set(0, row);
        n
    } else {
        nums
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

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let range = (hi - lo + 1) as u64;
        (self.next_u64() % range) as i32 + lo
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let range = (hi - lo + 1) as u64;
        (self.next_u64() % range) as usize + lo
    }
}

struct Solution;
include!("../code.rs");

/// Build a random jagged 2D array satisfying the problem constraints.
/// `total` is the total number of elements across all rows.
/// `num_rows` is the number of rows.
fn random_nums(rng: &mut Rng, num_rows: usize, total: usize) -> Vec<Vec<i32>> {
    // Distribute `total` elements across `num_rows` rows, each with >= 1 element
    let mut row_lens: Vec<usize> = Vec::new();
    let mut remaining = total;
    for i in 0..num_rows {
        let left = num_rows - i;
        let max_for_this = remaining - (left - 1); // leave at least 1 for each remaining row
        let len = if left == 1 {
            remaining
        } else {
            rng.gen_range_usize(1, max_for_this.min(100))
        };
        row_lens.push(len);
        remaining -= len;
    }

    let mut nums: Vec<Vec<i32>> = Vec::new();
    for &len in &row_lens {
        let mut row: Vec<i32> = Vec::new();
        for _ in 0..len {
            row.push(rng.gen_range_i32(1, 100_000));
        }
        nums.push(row);
    }
    nums
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<Vec<i32>>, seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let output = Solution::find_diagonal_order(nums.clone());
        writeln!(out, "{}", json!({
            "input": {"nums": nums},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<Vec<i32>>> = vec![
        vec![vec![1,2,3],vec![4,5,6],vec![7,8,9]],
        vec![vec![1,2,3,4,5],vec![6,7],vec![8],vec![9,10,11],vec![12,13,14,15,16]],
    ];
    for ex in examples {
        for mk in 0..=7u8 {
            let result = generate_test_case(ex.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Single row
    let single_row_cases: Vec<Vec<Vec<i32>>> = vec![
        vec![vec![1]],
        vec![vec![1, 2, 3, 4, 5]],
        vec![vec![100_000]],
    ];
    for tc in single_row_cases {
        for mk in 0..=7u8 {
            emit(generate_test_case(tc.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }

    // Single column (each row has 1 element)
    let single_col: Vec<Vec<i32>> = (1..=5).map(|v| vec![v]).collect();
    for mk in 0..=7u8 {
        emit(generate_test_case(single_col.clone(), mk), &mut seen, &mut out, &mut count);
    }

    // Square matrices of various sizes
    for &n in &[2usize, 3, 5, 10] {
        let mut mat: Vec<Vec<i32>> = Vec::new();
        let mut val = 1i32;
        for _ in 0..n {
            let mut row = Vec::new();
            for _ in 0..n {
                row.push(val);
                val = if val >= 100_000 { 1 } else { val + 1 };
            }
            mat.push(row);
        }
        for mk in 0..=7u8 {
            emit(generate_test_case(mat.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }

    // Jagged arrays with varying row lengths
    let jagged_configs: Vec<(usize, usize)> = vec![
        // (num_rows, total_elements)
        (2, 5),
        (3, 10),
        (5, 20),
        (10, 50),
        (20, 100),
        (50, 200),
        (5, 500),
        (10, 1000),
    ];
    for (nr, total) in jagged_configs {
        let nums = random_nums(&mut rng, nr, total);
        for mk in [0u8, 1, 3, 5, 6, 7] {
            emit(generate_test_case(nums.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }

    // Random cases with mutations
    while count < target {
        let num_rows = match rng.gen_range_usize(0, 4) {
            0 => 1,
            1 => rng.gen_range_usize(2, 5),
            2 => rng.gen_range_usize(2, 20),
            3 => rng.gen_range_usize(2, 50),
            _ => rng.gen_range_usize(2, 100),
        };
        let min_total = num_rows; // at least 1 element per row
        let max_total = (num_rows * 50).min(5000);
        let total = rng.gen_range_usize(min_total, max_total);
        let nums = random_nums(&mut rng, num_rows, total);
        let mk = rng.gen_range_usize(0, 7) as u8;
        emit(generate_test_case(nums, mk), &mut seen, &mut out, &mut count);
    }
}
