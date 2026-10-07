use vstd::prelude::*;

verus! {

pub open spec fn abs_diff(a: int, b: int) -> int { if a >= b { a - b } else { b - a } }
pub open spec fn move_cost(nums: Seq<i32>, cost: Seq<i32>, target: int, n: int) -> int
    recommends nums.len() == cost.len(), 0 <= n <= nums.len(),
    decreases n,
{
    if n <= 0 { 0 } else {
        move_cost(nums, cost, target, n - 1) + abs_diff(nums[n - 1] as int, target) * cost[n - 1] as int
    }
}
proof fn cost_append(nums: Seq<i32>, costs: Seq<i32>, x: i32, c: i32, target: int, end: int)
    requires nums.len() == costs.len(), 0 <= end <= nums.len(),
    ensures move_cost(nums.push(x), costs.push(c), target, end) == move_cost(nums, costs, target, end),
    decreases end,
{
    if end > 0 { cost_append(nums, costs, x, c, target, end - 1); }
}
pub fn generate_test_case(raw_nums: Vec<i32>, raw_cost: Vec<i32>) -> (result: (Vec<i32>, Vec<i32>))
    ensures 1 <= result.0.len() <= 100000, result.0.len() == result.1.len(),
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1000000,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 1000000,
        exists|target: int| 1 <= target <= 1000000 && #[trigger] move_cost(result.0@, result.1@, target, result.0.len() as int) <= 9007199254740991,
{
    let n = if raw_nums.len() == 0 { 1usize } else if raw_nums.len() > 100000 { 100000usize } else { raw_nums.len() };
    let target = if raw_nums.len() == 0 { 1 } else { raw_nums[0] };
    let target = if target < 1 { 1 } else if target > 1000000 { 1000000 } else { target };
    let mut nums: Vec<i32> = Vec::new();
    let mut costs: Vec<i32> = Vec::new();
    let mut total = 0i64;
    let mut i = 0usize;
    while i < n
        invariant i <= n, 1 <= n <= 100000, nums.len() == i, costs.len() == i,
            1 <= target <= 1000000,
            0 <= total <= 9007199254740991 - 1000000 * (n - i),
            total == move_cost(nums@, costs@, target as int, i as int),
            forall|j: int| 0 <= j < i ==> 1 <= #[trigger] nums[j] <= 1000000,
            forall|j: int| 0 <= j < i ==> 1 <= #[trigger] costs[j] <= 1000000,
        decreases n - i,
    {
        let x = if i < raw_nums.len() { raw_nums[i] } else { target };
        let x = if x < 1 { 1 } else if x > 1000000 { 1000000 } else { x };
        let c = if i < raw_cost.len() { raw_cost[i] } else { 1 };
        let c = if c < 1 { 1 } else if c > 1000000 { 1000000 } else { c };
        let distance = if x >= target { (x - target) as i64 } else { (target - x) as i64 };
        assert(0 <= distance * c <= 1000000000000) by(nonlinear_arith)
            requires 0 <= distance <= 999999, 1 <= c <= 1000000;
        let term = distance * (c as i64);
        let available = 9007199254740991i64 - total - 1000000 * ((n - i - 1) as i64);
        let c = if term <= available { c } else { 1 };
        proof { cost_append(nums@, costs@, x, c, target as int, i as int); }
        nums.push(x); costs.push(c);
        total += distance * (c as i64);
        i += 1;
    }
    let result = (nums, costs);
    assert(move_cost(result.0@, result.1@, target as int, result.0.len() as int) <= 9007199254740991);
    result
}


pub fn generate_candidate(
    nums_seed: &Vec<i32>,
    cost_seed: &Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= nums_seed.len() && nums_seed.len() <= 100_000,
        nums_seed.len() == cost_seed.len(),
        forall|i: int| 0 <= i && i < nums_seed.len() ==> 1 <= #[trigger] nums_seed[i] && nums_seed[i] <= 1_000_000,
        forall|i: int| 0 <= i && i < cost_seed.len() ==> 1 <= #[trigger] cost_seed[i] && cost_seed[i] <= 1_000_000,
    ensures
        1 <= result.0.len() && result.0.len() <= 100_000,
        result.0.len() == result.1.len(),
        forall|i: int| 0 <= i && i < result.0.len() ==> 1 <= #[trigger] result.0[i] && result.0[i] <= 1_000_000,
        forall|i: int| 0 <= i && i < result.1.len() ==> 1 <= #[trigger] result.1[i] && result.1[i] <= 1_000_000,
{
    let n = nums_seed.len();

    if mutation_kind == 1 {
        // set all nums to 1
        let mut nums: Vec<i32> = Vec::new();
        let mut cost: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n, n == nums_seed.len(), n == cost_seed.len(),
                1 <= n <= 100_000, nums.len() == k, cost.len() == k,
                forall|j: int| 0 <= j < k ==> #[trigger] nums[j] == 1i32,
                forall|j: int| 0 <= j < k ==> 1 <= #[trigger] nums[j] && nums[j] <= 1_000_000,
                forall|j: int| 0 <= j < k ==> 1 <= #[trigger] cost[j] && cost[j] <= 1_000_000,
                forall|i: int| 0 <= i && i < cost_seed.len() ==> 1 <= #[trigger] cost_seed[i] && cost_seed[i] <= 1_000_000,
            decreases n - k,
        {
            nums.push(1);
            cost.push(cost_seed[k]);
            k = k + 1;
        }
        (nums, cost)
    } else if mutation_kind == 2 {
        // set all nums to 1_000_000
        let mut nums: Vec<i32> = Vec::new();
        let mut cost: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n, n == nums_seed.len(), n == cost_seed.len(),
                1 <= n <= 100_000, nums.len() == k, cost.len() == k,
                forall|j: int| 0 <= j < k ==> #[trigger] nums[j] == 1_000_000i32,
                forall|j: int| 0 <= j < k ==> 1 <= #[trigger] nums[j] && nums[j] <= 1_000_000,
                forall|j: int| 0 <= j < k ==> 1 <= #[trigger] cost[j] && cost[j] <= 1_000_000,
                forall|i: int| 0 <= i && i < cost_seed.len() ==> 1 <= #[trigger] cost_seed[i] && cost_seed[i] <= 1_000_000,
            decreases n - k,
        {
            nums.push(1_000_000);
            cost.push(cost_seed[k]);
            k = k + 1;
        }
        (nums, cost)
    } else if mutation_kind == 3 {
        // set all costs to 1
        let mut nums: Vec<i32> = Vec::new();
        let mut cost: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n, n == nums_seed.len(), n == cost_seed.len(),
                1 <= n <= 100_000, nums.len() == k, cost.len() == k,
                forall|j: int| 0 <= j < k ==> #[trigger] cost[j] == 1i32,
                forall|j: int| 0 <= j < k ==> 1 <= #[trigger] nums[j] && nums[j] <= 1_000_000,
                forall|j: int| 0 <= j < k ==> 1 <= #[trigger] cost[j] && cost[j] <= 1_000_000,
                forall|i: int| 0 <= i && i < nums_seed.len() ==> 1 <= #[trigger] nums_seed[i] && nums_seed[i] <= 1_000_000,
            decreases n - k,
        {
            nums.push(nums_seed[k]);
            cost.push(1);
            k = k + 1;
        }
        (nums, cost)
    } else if mutation_kind == 4 {
        // set all costs to 1_000_000
        let mut nums: Vec<i32> = Vec::new();
        let mut cost: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n, n == nums_seed.len(), n == cost_seed.len(),
                1 <= n <= 100_000, nums.len() == k, cost.len() == k,
                forall|j: int| 0 <= j < k ==> #[trigger] cost[j] == 1_000_000i32,
                forall|j: int| 0 <= j < k ==> 1 <= #[trigger] nums[j] && nums[j] <= 1_000_000,
                forall|j: int| 0 <= j < k ==> 1 <= #[trigger] cost[j] && cost[j] <= 1_000_000,
                forall|i: int| 0 <= i && i < nums_seed.len() ==> 1 <= #[trigger] nums_seed[i] && nums_seed[i] <= 1_000_000,
            decreases n - k,
        {
            nums.push(nums_seed[k]);
            cost.push(1_000_000);
            k = k + 1;
        }
        (nums, cost)
    } else if mutation_kind == 5 {
        // nudge first num up
        let mut nums: Vec<i32> = Vec::new();
        let mut cost: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n, n == nums_seed.len(), n == cost_seed.len(),
                1 <= n <= 100_000, nums.len() == k, cost.len() == k,
                forall|j: int| 0 <= j < k ==> 1 <= #[trigger] nums[j] && nums[j] <= 1_000_000,
                forall|j: int| 0 <= j < k ==> 1 <= #[trigger] cost[j] && cost[j] <= 1_000_000,
                forall|i: int| 0 <= i && i < nums_seed.len() ==> 1 <= #[trigger] nums_seed[i] && nums_seed[i] <= 1_000_000,
                forall|i: int| 0 <= i && i < cost_seed.len() ==> 1 <= #[trigger] cost_seed[i] && cost_seed[i] <= 1_000_000,
            decreases n - k,
        {
            if k == 0 && nums_seed[0] < 1_000_000 {
                nums.push(nums_seed[0] + 1);
            } else {
                nums.push(nums_seed[k]);
            }
            cost.push(cost_seed[k]);
            k = k + 1;
        }
        (nums, cost)
    } else if mutation_kind == 6 {
        // nudge first num down
        let mut nums: Vec<i32> = Vec::new();
        let mut cost: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n, n == nums_seed.len(), n == cost_seed.len(),
                1 <= n <= 100_000, nums.len() == k, cost.len() == k,
                forall|j: int| 0 <= j < k ==> 1 <= #[trigger] nums[j] && nums[j] <= 1_000_000,
                forall|j: int| 0 <= j < k ==> 1 <= #[trigger] cost[j] && cost[j] <= 1_000_000,
                forall|i: int| 0 <= i && i < nums_seed.len() ==> 1 <= #[trigger] nums_seed[i] && nums_seed[i] <= 1_000_000,
                forall|i: int| 0 <= i && i < cost_seed.len() ==> 1 <= #[trigger] cost_seed[i] && cost_seed[i] <= 1_000_000,
            decreases n - k,
        {
            if k == 0 && nums_seed[0] > 1 {
                nums.push(nums_seed[0] - 1);
            } else {
                nums.push(nums_seed[k]);
            }
            cost.push(cost_seed[k]);
            k = k + 1;
        }
        (nums, cost)
    } else if mutation_kind == 7 {
        // set all nums equal to first element (zero-cost case)
        let first_val = nums_seed[0];
        let mut nums: Vec<i32> = Vec::new();
        let mut cost: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n, n == nums_seed.len(), n == cost_seed.len(),
                1 <= n <= 100_000, nums.len() == k, cost.len() == k,
                1 <= first_val && first_val <= 1_000_000,
                forall|j: int| 0 <= j < k ==> #[trigger] nums[j] == first_val,
                forall|j: int| 0 <= j < k ==> 1 <= #[trigger] nums[j] && nums[j] <= 1_000_000,
                forall|j: int| 0 <= j < k ==> 1 <= #[trigger] cost[j] && cost[j] <= 1_000_000,
                forall|i: int| 0 <= i && i < cost_seed.len() ==> 1 <= #[trigger] cost_seed[i] && cost_seed[i] <= 1_000_000,
            decreases n - k,
        {
            nums.push(first_val);
            cost.push(cost_seed[k]);
            k = k + 1;
        }
        (nums, cost)
    } else if mutation_kind == 8 && n > 1 {
        // swap first and last elements of nums
        let mut nums: Vec<i32> = Vec::new();
        let mut cost: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        let last = n - 1;
        while k < n
            invariant
                0 <= k <= n, n == nums_seed.len(), n == cost_seed.len(),
                1 <= n <= 100_000, last == n - 1, n > 1,
                nums.len() == k, cost.len() == k,
                forall|j: int| 0 <= j < k ==> 1 <= #[trigger] nums[j] && nums[j] <= 1_000_000,
                forall|j: int| 0 <= j < k ==> 1 <= #[trigger] cost[j] && cost[j] <= 1_000_000,
                forall|i: int| 0 <= i && i < nums_seed.len() ==> 1 <= #[trigger] nums_seed[i] && nums_seed[i] <= 1_000_000,
                forall|i: int| 0 <= i && i < cost_seed.len() ==> 1 <= #[trigger] cost_seed[i] && cost_seed[i] <= 1_000_000,
            decreases n - k,
        {
            if k == 0 {
                nums.push(nums_seed[last]);
            } else if k == last {
                nums.push(nums_seed[0]);
            } else {
                nums.push(nums_seed[k]);
            }
            cost.push(cost_seed[k]);
            k = k + 1;
        }
        (nums, cost)
    } else {
        // identity / fallback: copy both arrays
        let mut nums: Vec<i32> = Vec::new();
        let mut cost: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n, n == nums_seed.len(), n == cost_seed.len(),
                1 <= n <= 100_000, nums.len() == k, cost.len() == k,
                forall|j: int| 0 <= j < k ==> 1 <= #[trigger] nums[j] && nums[j] <= 1_000_000,
                forall|j: int| 0 <= j < k ==> 1 <= #[trigger] cost[j] && cost[j] <= 1_000_000,
                forall|i: int| 0 <= i && i < nums_seed.len() ==> 1 <= #[trigger] nums_seed[i] && nums_seed[i] <= 1_000_000,
                forall|i: int| 0 <= i && i < cost_seed.len() ==> 1 <= #[trigger] cost_seed[i] && cost_seed[i] <= 1_000_000,
            decreases n - k,
        {
            nums.push(nums_seed[k]);
            cost.push(cost_seed[k]);
            k = k + 1;
        }
        (nums, cost)
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

fn mutate(nums: &Vec<i32>, cost: &Vec<i32>, mk: u8) -> (Vec<i32>, Vec<i32>) {
    generate_candidate(nums, cost, mk)
}

fn random_array(rng: &mut Rng, len: usize, lo: i32, hi: i32) -> Vec<i32> {
    let mut arr = Vec::with_capacity(len);
    for _ in 0..len {
        arr.push(rng.gen_range_i64(lo as i64, hi as i64) as i32);
    }
    arr
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2448);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, cost: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        let key = format!("{:?}|{:?}", nums, cost);
        if !seen.insert(key) { return; }
        let (nums, cost) = generate_test_case(nums, cost);
        let output = Solution::min_cost(nums.clone(), cost.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums, "cost": cost}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let example_seeds: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![1, 3, 5, 2], vec![2, 3, 1, 14]),
        (vec![2, 2, 2, 2, 2], vec![4, 2, 8, 1, 3]),
    ];
    for (ns, cs) in &example_seeds {
        for mk in 0..=8u8 {
            let (nums, cost) = mutate(ns, cs, mk);
            emit(nums, cost, &mut seen, &mut out, &mut count);
        }
    }

    // Handcrafted seeds covering interesting cases
    let hand_seeds: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![1], vec![1]),
        (vec![1, 1_000_000], vec![1, 1]),
        (vec![500_000, 500_001], vec![1_000_000, 1_000_000]),
        (vec![1, 1, 1, 1, 1], vec![1, 1, 1, 1, 1]),
        (vec![1, 2, 3, 4, 5], vec![5, 4, 3, 2, 1]),
        (vec![1_000_000, 1_000_000], vec![1_000_000, 1_000_000]),
        (vec![1, 1], vec![1_000_000, 1_000_000]),
    ];
    for (ns, cs) in &hand_seeds {
        for mk in 0..=8u8 {
            let (nums, cost) = mutate(ns, cs, mk);
            emit(nums, cost, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds across size classes with all mutation kinds
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 3), (4, 10), (11, 100), (101, 1000), (1001, 5000),
    ];
    for &(lo, hi) in &size_classes {
        for _ in 0..3 {
            let n = rng.gen_range_usize(lo, hi);
            let nums_s = random_array(&mut rng, n, 1, 1_000_000);
            let cost_s = random_array(&mut rng, n, 1, 1_000_000);
            let mk = rng.gen_range_usize(0, 8) as u8;
            let (nums, cost) = mutate(&nums_s, &cost_s, mk);
            emit(nums, cost, &mut seen, &mut out, &mut count);
        }
    }

    // Fill remaining with random inputs and random mutations
    while count < target_count {
        let n = match count % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 5000),
        };
        let val_range = if count % 5 == 0 {
            let choices = [1i32, 1_000_000, 500_000, 1, 2];
            let pick = choices[rng.gen_range_usize(0, choices.len() - 1)];
            (pick, pick)
        } else {
            (1i32, 1_000_000i32)
        };
        let nums_s = random_array(&mut rng, n, val_range.0, val_range.1);
        let cost_s = random_array(&mut rng, n, 1, 1_000_000);
        let mk = rng.gen_range_usize(0, 8) as u8;
        let (nums, cost) = mutate(&nums_s, &cost_s, mk);
        emit(nums, cost, &mut seen, &mut out, &mut count);
    }

    eprintln!("Generated {} test cases to {:?}", count, out_path);
}
