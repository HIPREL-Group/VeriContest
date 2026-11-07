use vstd::prelude::*;

verus! {

pub open spec fn seen_in_suffix(nums: Seq<i32>, v: int, ops: int) -> bool {
    exists |q: int|
        0 <= q < ops
        && 0 <= nums.len() - ops + q < nums.len()
        && #[trigger] nums[nums.len() - ops + q] == v
}

pub open spec fn all_seen(nums: Seq<i32>, k: int, ops: int) -> bool {
    forall |v: int| 1 <= v <= k ==> seen_in_suffix(nums, v, ops)
}

pub fn generate_test_case(
    k_val: i32,
    fillers: &Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= k_val <= 50,
        k_val as int + fillers.len() as int >= 1,
        k_val as int + fillers.len() as int <= 50,
        forall |i: int| 0 <= i < fillers.len() ==>
            1 <= #[trigger] fillers[i] <= k_val as int + fillers.len() as int,
    ensures
        1 <= result.0.len() <= 50,
        1 <= result.1 <= result.0.len(),
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= result.0.len(),
        all_seen(result.0@, result.1 as int, result.0.len() as int),
{
    let n: usize = k_val as usize + fillers.len();
    let mut nums: Vec<i32> = Vec::new();

    let mut v: i32 = 1;
    while v <= k_val
        invariant
            1 <= v <= k_val as int + 1,
            nums.len() == (v - 1) as nat,
            n == k_val as usize + fillers.len(),
            1 <= n <= 50,
            forall |j: int| 0 <= j < nums.len() as int ==>
                #[trigger] nums@[j] == (j + 1),
            forall |j: int| 0 <= j < nums.len() as int ==>
                1 <= #[trigger] nums[j] <= n as int,
        decreases k_val - v + 1,
    {
        nums.push(v);
        v += 1;
    }

    let mut fi: usize = 0;
    while fi < fillers.len()
        invariant
            0 <= fi <= fillers.len(),
            nums.len() == k_val as usize + fi,
            n == k_val as usize + fillers.len(),
            1 <= n <= 50,
            1 <= k_val <= 50,
            k_val as int + fillers.len() as int <= 50,
            n as int == k_val as int + fillers.len() as int,
            forall |i: int| 0 <= i < fillers.len() ==>
                1 <= #[trigger] fillers[i] <= n as int,
            forall |j: int| 0 <= j < k_val as int ==>
                #[trigger] nums@[j] == (j + 1),
            forall |j: int| 0 <= j < nums.len() as int ==>
                1 <= #[trigger] nums[j] <= n as int,
        decreases fillers.len() - fi,
    {
        assert(1 <= fillers[fi as int] <= n as int);
        nums.push(fillers[fi]);
        fi += 1;
    }

    if mutation_kind == 1 && fillers.len() > 0 {
        let idx = k_val as usize;
        nums.set(idx, 1);
    } else if mutation_kind == 2 && fillers.len() > 0 {
        let idx = k_val as usize;
        nums.set(idx, k_val);
    } else if mutation_kind == 3 && fillers.len() > 0 {
        let idx = k_val as usize;
        nums.set(idx, n as i32);
    } else if mutation_kind == 4 && fillers.len() >= 2 {
        let idx0 = k_val as usize;
        let idx1 = k_val as usize + 1;
        nums.set(idx0, 1);
        nums.set(idx1, n as i32);
    }

    proof {
        assert forall |w: int| 1 <= w <= k_val as int
            implies seen_in_suffix(nums@, w, nums@.len() as int) by {
            let q = w - 1;
            assert(0 <= q < nums@.len() as int);
            assert(nums@.len() as int - nums@.len() as int + q == q);
            assert(nums@[q] == w);
        }
    }

    (nums, k_val)
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

fn gen(k_val: i32, fillers: &Vec<i32>, mutation_kind: u8) -> (Vec<i32>, i32) {
    generate_test_case(k_val, fillers, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2869);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |nums: Vec<i32>, k: i32, seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count { return; }
        let key = format!("{:?}_{}", nums, k);
        if !seen.insert(key) { return; }
        let output = Solution::min_operations(nums.clone(), k);
        writeln!(out, "{}", json!({"input": {"nums": nums, "k": k}, "output": output})).unwrap();
        *emitted += 1;
    };

    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![3, 1, 5, 4, 2], 2),
        (vec![3, 1, 5, 4, 2], 5),
        (vec![3, 2, 5, 3, 1], 3),
    ];
    for (nums, k) in examples {
        emit(nums, k, &mut seen, &mut out, &mut emitted);
    }

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4];

    for k in 1..=10i32 {
        for &mk in &mutation_kinds {
            if emitted >= count { break; }
            let fillers: Vec<i32> = vec![];
            let (nums, k_out) = gen(k, &fillers, mk);
            emit(nums, k_out, &mut seen, &mut out, &mut emitted);
        }
    }

    while emitted < count {
        let k: i32 = match emitted % 5 {
            0 => 1,
            1 => rng.gen_range_i64(1, 3) as i32,
            2 => rng.gen_range_i64(1, 10) as i32,
            3 => rng.gen_range_i64(5, 25) as i32,
            _ => rng.gen_range_i64(10, 50) as i32,
        };
        let max_n = 50i32.min(k + 20);
        let n: i32 = if k >= 50 { k } else { rng.gen_range_i64(k as i64, max_n as i64) as i32 };
        let n_fillers = (n - k) as usize;
        let mut fillers: Vec<i32> = Vec::with_capacity(n_fillers);
        for _ in 0..n_fillers {
            fillers.push(rng.gen_range_i64(1, n as i64) as i32);
        }
        let mk = (rng.next_u64() % 5) as u8;
        let (nums, k_out) = gen(k, &fillers, mk);
        emit(nums, k_out, &mut seen, &mut out, &mut emitted);
    }
}
