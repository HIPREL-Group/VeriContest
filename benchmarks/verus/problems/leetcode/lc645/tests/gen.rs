use vstd::prelude::*;

verus! {

pub open spec fn appears_in(s: Seq<i32>, val: i32) -> bool {
    exists |j: int| 0 <= j < s.len() && #[trigger] s[j] == val
}

pub open spec fn appears_twice(s: Seq<i32>, val: i32) -> bool {
    exists |j1: int, j2: int| 0 <= j1 < j2 < s.len()
        && #[trigger] s[j1] == val && #[trigger] s[j2] == val
}

pub fn generate_test_case(
    n: usize,
    dup_val: usize,
    replace_pos: usize,
    mutation_kind: u8,
) -> (result: Vec<i32>)
    requires
        2 <= n <= 10_000,
        1 <= dup_val <= n,
        0 <= replace_pos < n,
        replace_pos != dup_val - 1,
    ensures
        2 <= result.len() <= 10_000,
        forall |i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= result.len(),
        exists |d: int| 1 <= d <= result.len() && #[trigger] appears_twice(result@, d as i32),
        exists |m: int| 1 <= m <= result.len() && !#[trigger] appears_in(result@, m as i32),
        forall |v1: i32, v2: i32|
            appears_twice(result@, v1) && appears_twice(result@, v2) ==> v1 == v2,
        forall |v1: int, v2: int|
            1 <= v1 <= result.len() && 1 <= v2 <= result.len()
            && !#[trigger] appears_in(result@, v1 as i32) && !#[trigger] appears_in(result@, v2 as i32)
            ==> v1 == v2,
{
    // Select effective replace position based on mutation
    let rp: usize = if mutation_kind == 1 && dup_val < n {
        n - 1
    } else if mutation_kind == 2 && dup_val > 1 {
        0
    } else {
        replace_pos
    };

    // Build array [1, 2, ..., n]
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            nums.len() == i,
            2 <= n <= 10_000,
            forall |j: int| 0 <= j < i as int ==> nums@[j] == (j + 1) as i32,
        decreases n - i,
    {
        nums.push((i + 1) as i32);
        i = i + 1;
    }

    // Overwrite position rp with dup_val to create the duplicate/missing pair
    nums.set(rp, dup_val as i32);

    proof {
        // Key structural fact: for j != rp, nums@[j] == (j+1); nums@[rp] == dup_val
        // The missing value is rp+1, the duplicate value is dup_val.

        // (1) All values in [1, n]
        assert forall |j: int| 0 <= j < nums.len()
            implies 1 <= #[trigger] nums@[j] <= nums.len() as i32
        by {
            if j == rp as int {
                assert(nums@[j] == dup_val as i32);
            } else {
                assert(nums@[j] == (j + 1) as i32);
            }
        };

        // (2) dup_val appears at positions dup_val-1 and rp
        assert((dup_val - 1) as int != rp as int);
        assert(nums@[(dup_val - 1) as int] == dup_val as i32);
        assert(nums@[rp as int] == dup_val as i32);
        if (dup_val - 1) < rp {
            let j1: int = (dup_val - 1) as int;
            let j2: int = rp as int;
            assert(0 <= j1);
            assert(j1 < j2);
            assert(j2 < nums.len());
            assert(nums@[j1] == dup_val as i32);
            assert(nums@[j2] == dup_val as i32);
        } else {
            let j1: int = rp as int;
            let j2: int = (dup_val - 1) as int;
            assert(0 <= j1);
            assert(j1 < j2);
            assert(j2 < nums.len());
            assert(nums@[j1] == dup_val as i32);
            assert(nums@[j2] == dup_val as i32);
        }
        assert(appears_twice(nums@, dup_val as i32));

        // (3) Value rp+1 does not appear
        assert forall |j: int| 0 <= j < nums.len()
            implies nums@[j] != (rp + 1) as i32
        by {
            if j == rp as int {
                assert(nums@[j] == dup_val as i32);
            } else {
                assert(nums@[j] == (j + 1) as i32);
            }
        };
        assert(!appears_in(nums@, (rp + 1) as i32));

        // (4) Any two positions with equal values must involve rp, value = dup_val
        assert forall |j1: int, j2: int|
            0 <= j1 < j2 < nums.len() as int && nums@[j1] == nums@[j2]
            implies nums@[j1] == dup_val as i32
        by {
            if j1 != rp as int && j2 != rp as int {
                assert(nums@[j1] == (j1 + 1) as i32);
                assert(nums@[j2] == (j2 + 1) as i32);
            } else if j1 == rp as int {
                assert(nums@[j1] == dup_val as i32);
            } else {
                assert(nums@[j2] == dup_val as i32);
            }
        };

        // (5) For any v in [1,n] with v != rp+1, v appears in nums
        assert forall |v: int|
            1 <= v <= nums.len() && v != rp as int + 1
            implies #[trigger] appears_in(nums@, v as i32)
        by {
            if v == dup_val as int {
                assert(0 <= (dup_val - 1) as int);
                assert(((dup_val - 1) as int) < (nums.len() as int));
                assert(nums@[(dup_val - 1) as int] == v as i32);
            } else {
                assert((v - 1) as int != rp as int);
                assert(0 <= v - 1);
                assert(v - 1 < nums.len());
                assert(nums@[v - 1] == v as i32);
            }
        };

        // (6) Uniqueness of missing: !appears_in(v) implies v == rp+1
        assert forall |v1: int, v2: int|
            1 <= v1 <= nums.len() && 1 <= v2 <= nums.len()
            && !#[trigger] appears_in(nums@, v1 as i32) && !#[trigger] appears_in(nums@, v2 as i32)
            implies v1 == v2
        by {
            // By (5), !appears_in(v) implies v == rp+1
            // So both v1 and v2 must equal rp+1
            if v1 != rp as int + 1 {
                assert(appears_in(nums@, v1 as i32));
            }
            if v2 != rp as int + 1 {
                assert(appears_in(nums@, v2 as i32));
            }
        };
    }

    nums
}

} // verus!

fn gen(n: usize, dup_val: usize, replace_pos: usize, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(n, dup_val, replace_pos, mutation_kind)
}

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
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(645);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>, total: &mut usize| {
        if *total >= count { return; }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let output = Solution::find_error_nums(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *total += 1;
    };

    // Example test cases from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 2, 2, 4],
        vec![1, 1],
    ];
    for ex in examples {
        emit(ex, &mut seen, &mut out, &mut total);
    }

    // Hand-crafted seeds: (n, dup_val, replace_pos)
    let manual_seeds: Vec<(usize, usize, usize)> = vec![
        (2, 1, 1),       // [1,1]
        (2, 2, 0),       // [2,2]
        (3, 1, 1),       // [1,1,3]
        (3, 1, 2),       // [1,2,1]
        (3, 3, 0),       // [3,2,3]
        (3, 2, 0),       // [2,2,3]
        (4, 2, 2),       // [1,2,2,4]
        (5, 3, 0),       // [3,2,3,4,5]
        (5, 5, 0),       // [5,2,3,4,5]
        (10, 1, 9),      // dup=1 at last pos
        (10, 10, 0),     // dup=10 at first pos
        (100, 50, 0),    // medium
        (1000, 500, 999), // large
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2];
    for &(n, dv, rp) in &manual_seeds {
        for &mk in &mutation_kinds {
            if total >= count { break; }
            let result = gen(n, dv, rp, mk);
            emit(result, &mut seen, &mut out, &mut total);
        }
    }

    // Random test cases with diverse size classes
    let mut _attempts_0 = 0usize;
    while total < count {
        _attempts_0 += 1; if _attempts_0 > 10000 { break; }
        let n: usize = match total % 5 {
            0 => rng.gen_range_usize(2, 5),          // tiny
            1 => rng.gen_range_usize(2, 10),         // small
            2 => rng.gen_range_usize(11, 100),       // medium
            3 => rng.gen_range_usize(101, 1000),     // large
            _ => rng.gen_range_usize(1001, 10_000),  // max
        };
        let dup_val = rng.gen_range_usize(1, n);
        let mut rp = rng.gen_range_usize(0, n - 1);
        if rp == dup_val - 1 {
            rp = (rp + 1) % n;
        }
        let mk = rng.gen_range_usize(0, 2) as u8;
        let result = gen(n, dup_val, rp, mk);
        emit(result, &mut seen, &mut out, &mut total);
    }
}
