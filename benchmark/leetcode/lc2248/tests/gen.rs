use vstd::prelude::*;

verus! {

pub open spec fn total_len(nums: Seq<Seq<i32>>, end: int) -> int
    decreases end,
{
    if end <= 0 { 0 } else { total_len(nums, end - 1) + nums[end - 1].len() as int }
}
proof fn row_sum_append(rows: Seq<Seq<i32>>, row: Seq<i32>, end: int)
    requires 0 <= end <= rows.len(),
    ensures total_len(rows.push(row), end) == total_len(rows, end),
    decreases end,
{
    if end > 0 { row_sum_append(rows, row, end - 1); }
}
fn unique_row(raw: &Vec<i32>, budget: usize) -> (result: Vec<i32>)
    requires 1 <= budget <= 1000,
    ensures 1 <= result.len() <= budget,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1000,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
{
    let end = if raw.len() > budget { budget } else { raw.len() };
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0usize;
    while i < end
        invariant i <= end <= raw.len(), end <= budget, 1 <= budget <= 1000, result.len() <= i,
            forall|j: int| 0 <= j < result.len() ==> 1 <= #[trigger] result[j] <= 1000,
            forall|j: int, k: int| 0 <= j < k < result.len() ==> result[j] != result[k],
        decreases end - i,
    {
        let v = raw[i];
        let v = if v < 1 { 1 } else if v > 1000 { 1000 } else { v };
        let mut found = false;
        let mut j = 0usize;
        while j < result.len()
            invariant j <= result.len(),
                !found ==> forall|k: int| 0 <= k < j ==> #[trigger] result[k] != v,
            decreases result.len() - j,
        {
            if result[j] == v { found = true; }
            j += 1;
        }
        if !found { result.push(v); }
        i += 1;
    }
    if result.len() == 0 { result.push(1); }
    result
}
pub fn generate_test_case(raw: Vec<Vec<i32>>) -> (result: Vec<Vec<i32>>)
    ensures 1 <= result.len() <= 1000,
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() >= 1,
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() ==> 1 <= #[trigger] result[i][j] <= 1000,
        1 <= total_len(result.deep_view(), result.len() as int) <= 1000,
        forall|i: int, j: int, k: int| 0 <= i < result.len() && 0 <= j < k < result[i].len() ==> result[i][j] != result[i][k],
{
    let n = if raw.len() == 0 { 1usize } else if raw.len() > 1000 { 1000usize } else { raw.len() };
    let empty: Vec<i32> = Vec::new();
    let mut result: Vec<Vec<i32>> = Vec::new();
    let mut total = 0usize;
    let mut i = 0usize;
    while i < n
        invariant i <= n, 1 <= n <= 1000, result.len() == i,
            i <= total <= 1000 - (n - i), total == total_len(result.deep_view(), i as int),
            forall|j: int| 0 <= j < i ==> #[trigger] result[j].len() >= 1,
            forall|j: int, k: int| 0 <= j < i && 0 <= k < result[j].len() ==> 1 <= #[trigger] result[j][k] <= 1000,
            forall|j: int, k: int, l: int| 0 <= j < i && 0 <= k < l < result[j].len() ==> result[j][k] != result[j][l],
        decreases n - i,
    {
        let budget = 1000 - total - (n - i - 1);
        let row = unique_row(if i < raw.len() { &raw[i] } else { &empty }, budget);
        let ghost rows = result.deep_view();
        let ghost row_view = row.deep_view();
        total += row.len();
        result.push(row);
        proof {
            assert(result.deep_view() =~= rows.push(row_view));
            row_sum_append(rows, row_view, i as int);
        }
        i += 1;
    }
    result
}


pub fn generate_candidate(
    nums: Vec<Vec<i32>>,
    mutation_kind: u8,
) -> (result: Vec<Vec<i32>>)
    requires
        1 <= nums.len() <= 1000,
        forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i].len() >= 1,
        forall|i: int, j: int|
            0 <= i < nums.len() && 0 <= j < nums[i].len()
                ==> 1 <= #[trigger] nums[i][j] <= 1000,
    ensures
        1 <= result.len() <= 1000,
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() >= 1,
        forall|i: int, j: int|
            0 <= i < result.len() && 0 <= j < result[i].len()
                ==> 1 <= #[trigger] result[i][j] <= 1000,
{
    if mutation_kind == 0 {
        nums
    } else if mutation_kind == 1 && nums.len() < 1000 {
        // push a new single-element row [500]
        let mut result = nums;
        let mut new_row: Vec<i32> = Vec::new();
        new_row.push(500i32);
        let ghost old_len = result.len();
        result.push(new_row);
        proof {
            assert(result.len() == old_len + 1);
            assert forall|i: int|
                0 <= i < result.len() implies #[trigger] result[i].len() >= 1
            by {
                if i < old_len as int {
                    assert(result[i] == nums[i]);
                } else {
                    assert(i == old_len as int);
                }
            };
            assert forall|i: int, j: int|
                0 <= i < result.len() && 0 <= j < result[i].len()
                    implies 1 <= #[trigger] result[i][j] <= 1000
            by {
                if i < old_len as int {
                    assert(result[i] == nums[i]);
                    assert(result[i][j] == nums[i][j]);
                } else {
                    assert(i == old_len as int);
                    assert(result[i][j] == 500i32);
                }
            };
        }
        result
    } else if mutation_kind == 2 && nums.len() > 1 {
        // pop last row
        let mut result = nums;
        let ghost old_len = result.len();
        result.pop();
        proof {
            assert(result.len() == old_len - 1);
            assert(result.len() >= 1);
            assert forall|i: int|
                0 <= i < result.len() implies #[trigger] result[i].len() >= 1
            by {
                assert(result[i] == nums[i]);
            };
            assert forall|i: int, j: int|
                0 <= i < result.len() && 0 <= j < result[i].len()
                    implies 1 <= #[trigger] result[i][j] <= 1000
            by {
                assert(result[i] == nums[i]);
                assert(result[i][j] == nums[i][j]);
            };
        }
        result
    } else if mutation_kind == 3 {
        // replace first row with [1]
        let mut result = nums;
        let mut new_row: Vec<i32> = Vec::new();
        new_row.push(1i32);
        result.set(0, new_row);
        proof {
            assert(result.len() == nums.len());
            assert forall|i: int|
                0 <= i < result.len() implies #[trigger] result[i].len() >= 1
            by {
                if i == 0 {
                    assert(result[0].len() == 1);
                } else {
                    assert(result[i] == nums[i]);
                }
            };
            assert forall|i: int, j: int|
                0 <= i < result.len() && 0 <= j < result[i].len()
                    implies 1 <= #[trigger] result[i][j] <= 1000
            by {
                if i == 0 {
                    assert(result[0][0] == 1i32);
                } else {
                    assert(result[i] == nums[i]);
                    assert(result[i][j] == nums[i][j]);
                }
            };
        }
        result
    } else if mutation_kind == 4 {
        // replace first row with [1000]
        let mut result = nums;
        let mut new_row: Vec<i32> = Vec::new();
        new_row.push(1000i32);
        result.set(0, new_row);
        proof {
            assert(result.len() == nums.len());
            assert forall|i: int|
                0 <= i < result.len() implies #[trigger] result[i].len() >= 1
            by {
                if i == 0 {
                    assert(result[0].len() == 1);
                } else {
                    assert(result[i] == nums[i]);
                }
            };
            assert forall|i: int, j: int|
                0 <= i < result.len() && 0 <= j < result[i].len()
                    implies 1 <= #[trigger] result[i][j] <= 1000
            by {
                if i == 0 {
                    assert(result[0][0] == 1000i32);
                } else {
                    assert(result[i] == nums[i]);
                    assert(result[i][j] == nums[i][j]);
                }
            };
        }
        result
    } else if mutation_kind == 5 && nums.len() < 1000 {
        // push a row with boundary values [1, 500, 1000]
        let mut result = nums;
        let mut new_row: Vec<i32> = Vec::new();
        new_row.push(1i32);
        new_row.push(500i32);
        new_row.push(1000i32);
        let ghost old_len = result.len();
        result.push(new_row);
        proof {
            assert(result.len() == old_len + 1);
            assert forall|i: int|
                0 <= i < result.len() implies #[trigger] result[i].len() >= 1
            by {
                if i < old_len as int {
                    assert(result[i] == nums[i]);
                } else {
                    assert(i == old_len as int);
                    assert(result[i].len() == 3);
                }
            };
            assert forall|i: int, j: int|
                0 <= i < result.len() && 0 <= j < result[i].len()
                    implies 1 <= #[trigger] result[i][j] <= 1000
            by {
                if i < old_len as int {
                    assert(result[i] == nums[i]);
                    assert(result[i][j] == nums[i][j]);
                } else {
                    assert(i == old_len as int);
                    if j == 0 {
                        assert(result[i][j] == 1i32);
                    } else if j == 1 {
                        assert(result[i][j] == 500i32);
                    } else {
                        assert(j == 2);
                        assert(result[i][j] == 1000i32);
                    }
                }
            };
        }
        result
    } else if mutation_kind == 6 {
        // replace first row with [1, 500, 1000]
        let mut result = nums;
        let mut new_row: Vec<i32> = Vec::new();
        new_row.push(1i32);
        new_row.push(500i32);
        new_row.push(1000i32);
        result.set(0, new_row);
        proof {
            assert(result.len() == nums.len());
            assert forall|i: int|
                0 <= i < result.len() implies #[trigger] result[i].len() >= 1
            by {
                if i == 0 {
                    assert(result[0].len() == 3);
                } else {
                    assert(result[i] == nums[i]);
                }
            };
            assert forall|i: int, j: int|
                0 <= i < result.len() && 0 <= j < result[i].len()
                    implies 1 <= #[trigger] result[i][j] <= 1000
            by {
                if i == 0 {
                    if j == 0 {
                        assert(result[0][0] == 1i32);
                    } else if j == 1 {
                        assert(result[0][1] == 500i32);
                    } else {
                        assert(j == 2);
                        assert(result[0][2] == 1000i32);
                    }
                } else {
                    assert(result[i] == nums[i]);
                    assert(result[i][j] == nums[i][j]);
                }
            };
        }
        result
    } else if mutation_kind == 7 {
        // replace last row with [1]
        let mut result = nums;
        let last = result.len() - 1;
        let mut new_row: Vec<i32> = Vec::new();
        new_row.push(1i32);
        result.set(last, new_row);
        proof {
            assert(result.len() == nums.len());
            assert forall|i: int|
                0 <= i < result.len() implies #[trigger] result[i].len() >= 1
            by {
                if i == last as int {
                    assert(result[last as int].len() == 1);
                } else {
                    assert(result[i] == nums[i]);
                }
            };
            assert forall|i: int, j: int|
                0 <= i < result.len() && 0 <= j < result[i].len()
                    implies 1 <= #[trigger] result[i][j] <= 1000
            by {
                if i == last as int {
                    assert(result[last as int][0] == 1i32);
                } else {
                    assert(result[i] == nums[i]);
                    assert(result[i][j] == nums[i][j]);
                }
            };
        }
        result
    } else {
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

fn mutate(nums: Vec<Vec<i32>>, mutation_kind: u8) -> Vec<Vec<i32>> {
    generate_candidate(nums, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_row(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut row = Vec::with_capacity(len);
    for _ in 0..len {
        row.push(rng.gen_range_i64(1, 1000) as i32);
    }
    row
}

fn random_nums(rng: &mut Rng, n_rows: usize, min_cols: usize, max_cols: usize) -> Vec<Vec<i32>> {
    let mut nums = Vec::with_capacity(n_rows);
    for _ in 0..n_rows {
        let cols = rng.gen_range_usize(min_cols, max_cols);
        nums.push(random_row(rng, cols));
    }
    nums
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2248);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0usize;

    let mut emit = |nums: Vec<Vec<i32>>,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    total: &mut usize| {
        let nums = generate_test_case(nums);
        if *total >= count {
            return;
        }
        let key = format!("{:?}", nums);
        if !seen.insert(key) {
            return;
        }
        let result = Solution::intersection(nums.clone());
        writeln!(
            out,
            "{}",
            json!({"input": {"nums": nums}, "output": result})
        )
        .unwrap();
        *total += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<Vec<i32>>> = vec![
        vec![vec![3, 1, 2, 4, 5], vec![1, 2, 3, 4], vec![3, 4, 5, 6]],
        vec![vec![1, 2, 3], vec![4, 5, 6]],
    ];
    for ex in examples {
        for mk in 0u8..=8 {
            emit(mutate(ex.clone(), mk), &mut seen, &mut out, &mut total);
        }
    }

    // Curated seed inputs for edge cases
    let seeds: Vec<Vec<Vec<i32>>> = vec![
        vec![vec![1]],
        vec![vec![1000]],
        vec![vec![1, 2, 3, 4, 5]],
        vec![vec![1], vec![1]],
        vec![vec![1], vec![2]],
        vec![vec![1, 2], vec![2, 3], vec![3, 4]],
        vec![vec![500, 501], vec![500, 501]],
        vec![vec![1, 1000], vec![1, 1000], vec![1, 1000]],
    ];
    for s in seeds {
        for mk in 0u8..=8 {
            emit(mutate(s.clone(), mk), &mut seen, &mut out, &mut total);
        }
    }

    // Random inputs with diverse size classes
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];
    while total < count {
        let n_rows: usize = match total % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 50),
            3 => rng.gen_range_usize(51, 200),
            _ => rng.gen_range_usize(201, 1000),
        };
        let max_cols: usize = match total % 4 {
            0 => 1,
            1 => rng.gen_range_usize(1, 5),
            2 => rng.gen_range_usize(1, 20),
            _ => rng.gen_range_usize(1, 100),
        };
        let nums = random_nums(&mut rng, n_rows, 1, max_cols.max(1));
        let mk = mutation_kinds[rng.gen_range_usize(0, mutation_kinds.len() - 1)];
        emit(mutate(nums, mk), &mut seen, &mut out, &mut total);
    }
}
