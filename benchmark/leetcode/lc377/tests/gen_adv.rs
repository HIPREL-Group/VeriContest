use vstd::prelude::*;

verus! {


    pub open spec fn contribution(nums: Seq<i32>, target: nat, idx: nat) -> int
        decreases target, idx,
    {
        if idx < nums.len() as nat && 0 < nums[idx as int] as int <= target as int {
            combination_count(nums, ((target as int) - nums[idx as int] as int) as nat)
        } else {
            0
        }
    }

    pub open spec fn prefix_count(nums: Seq<i32>, target: nat, end: nat) -> int
        decreases target, end,
    {
        if end == 0 {
            0
        } else {
            prefix_count(nums, target, (end - 1) as nat)
                + contribution(nums, target, (end - 1) as nat)
        }
    }

    pub open spec fn combination_count(nums: Seq<i32>, target: nat) -> int
        decreases target,
    {
        if target == 0 {
            1
        } else {
            prefix_count(nums, target, nums.len() as nat)
        }
    }


fn bounded_target(nums: &Vec<i32>, target: i32) -> (result: i32)
    requires 1 <= nums.len() <= 200, 1 <= target <= 1000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
    ensures 1 <= result <= target, combination_count(nums@, result as nat) <= i32::MAX,
{
    let mut dp: Vec<i64> = Vec::new();
    dp.push(1);
    let mut t = 1usize;
    while t <= target as usize
        invariant 1 <= t <= target + 1, 1 <= target <= 1000, 1 <= nums.len() <= 200,
            dp.len() == t, dp[0] == 1,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
            forall|i: int| 0 <= i < t ==> 0 <= #[trigger] dp[i] <= i32::MAX,
            forall|i: int| 0 <= i < t ==> #[trigger] dp[i] == combination_count(nums@, i as nat),
        decreases target + 1 - t,
    {
        let mut sum = 0i64;
        let mut j = 0usize;
        while j < nums.len()
            invariant j <= nums.len() <= 200, 1 <= t <= target <= 1000,
                dp.len() == t, dp[0] == 1,
                forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
                forall|i: int| 0 <= i < t ==> 0 <= #[trigger] dp[i] <= i32::MAX,
                forall|i: int| 0 <= i < t ==> #[trigger] dp[i] == combination_count(nums@, i as nat),
                0 <= sum <= j * 2147483647,
                sum == prefix_count(nums@, t as nat, j as nat),
                t == 1 ==> sum <= j,
            decreases nums.len() - j,
        {
            let add = if nums[j] as usize <= t {
                let k = t - nums[j] as usize;
                assert(dp[k as int] == combination_count(nums@, k as nat));
                dp[k]
            } else { 0 };
            assert(add == contribution(nums@, t as nat, j as nat));
            sum += add;
            j += 1;
        }
        if sum > 2147483647 {
            assert(t > 1);
            assert(dp[t as int - 1] == combination_count(nums@, (t - 1) as nat));
            return (t - 1) as i32;
        }
        dp.push(sum);
        t += 1;
    }
    assert(dp[target as int] == combination_count(nums@, target as nat));
    target
}
pub fn generate_test_case(raw: Vec<i32>, target: i32) -> (result: (Vec<i32>, i32))
    ensures 1 <= result.0.len() <= 200,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1000,
        forall|i: int, j: int| 0 <= i < j < result.0.len() ==> result.0[i] != result.0[j],
        1 <= result.1 <= 1000, combination_count(result.0@, result.1 as nat) <= i32::MAX,
{
    let end = if raw.len() > 200 { 200usize } else { raw.len() };
    let mut nums: Vec<i32> = Vec::new();
    let mut i = 0usize;
    while i < end
        invariant i <= end <= raw.len(), end <= 200, nums.len() <= i,
            forall|j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 1000,
            forall|j: int, k: int| 0 <= j < k < nums.len() ==> nums[j] != nums[k],
        decreases end - i,
    {
        let v = raw[i];
        let v = if v < 1 { 1 } else if v > 1000 { 1000 } else { v };
        let mut found = false;
        let mut j = 0usize;
        while j < nums.len()
            invariant j <= nums.len(),
                !found ==> forall|k: int| 0 <= k < j ==> #[trigger] nums[k] != v,
            decreases nums.len() - j,
        { if nums[j] == v { found = true; } j += 1; }
        if !found { nums.push(v); }
        i += 1;
    }
    if nums.len() == 0 { nums.push(1); }
    let target = if target < 1 { 1 } else if target > 1000 { 1000 } else { target };
    let target = bounded_target(&nums, target);
    (nums, target)
}


pub fn generate_candidate(
    nums_in: &Vec<i32>,
    target: i32,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= nums_in.len() <= 200,
        forall |i: int| 0 <= i < nums_in.len() ==> 1 <= #[trigger] nums_in[i] <= 1000,
        forall |i: int, j: int| 0 <= i < j < nums_in.len() ==> nums_in[i] != nums_in[j],
        1 <= target <= 1000,
    ensures
        ({
            let (nums, tgt) = result;
            &&& 1 <= nums.len() <= 200
            &&& (forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000)
            &&& (forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] != nums[j])
            &&& 1 <= tgt <= 1000
            &&& tgt == target
            &&& nums@ == nums_in@
        }),
{
    let mut nums: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    while idx < nums_in.len()
        invariant
            0 <= idx <= nums_in.len(),
            nums.len() == idx,
            forall |k: int| 0 <= k < idx as int ==> #[trigger] nums[k] == nums_in[k],
        decreases nums_in.len() - idx,
    {
        nums.push(nums_in[idx]);
        idx += 1;
    }

    assert(nums@ =~= nums_in@);

    (nums, target)
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(0x9E3779B97F4A7C15) }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn make_distinct_nums(rng: &mut Rng, n: usize, max_val: i32) -> Vec<i32> {
    let mut res: Vec<i32> = Vec::with_capacity(n);
    let mut attempts = 0;
    while res.len() < n && attempts < 100000 {
        let v = rng.gen_range_i32(1, max_val);
        let mut found = false;
        for &u in &res {
            if u == v {
                found = true;
                break;
            }
        }
        if !found {
            res.push(v);
        }
        attempts += 1;
    }
    // Fill remainder sequentially if we couldn't get enough unique
    let mut candidate: i32 = 1;
    while res.len() < n {
        let mut found = false;
        for &u in &res {
            if u == candidate {
                found = true;
                break;
            }
        }
        if !found {
            res.push(candidate);
        }
        candidate += 1;
        if candidate > 1000 {
            break;
        }
    }
    res
}

fn adversarial_mode(rng: &mut Rng, mode: usize) -> (Vec<i32>, i32) {
    match mode {
        0 => {
            // Small case: [1,2,3], target=4
            (vec![1, 2, 3], 4)
        }
        1 => {
            // Single element not dividing target
            (vec![9], 3)
        }
        2 => {
            // Single element equal to target
            let t = rng.gen_range_i32(1, 1000);
            (vec![t], t)
        }
        3 => {
            // target = 1, nums contains 1
            let n = rng.gen_range_usize(1, 50);
            let mut nums = make_distinct_nums(rng, n, 1000);
            // ensure 1 is present
            let mut has_one = false;
            for &u in &nums {
                if u == 1 { has_one = true; break; }
            }
            if !has_one && !nums.is_empty() {
                nums[0] = 1;
            }
            (nums, 1)
        }
        4 => {
            // max target 1000, small nums
            let n = rng.gen_range_usize(1, 10);
            let nums = make_distinct_nums(rng, n, 1000);
            (nums, 1000)
        }
        5 => {
            // large nums array (up to 200)
            let nums = make_distinct_nums(rng, 200, 1000);
            let t = rng.gen_range_i32(1, 1000);
            (nums, t)
        }
        6 => {
            // All nums > target (result should be 0)
            let t = rng.gen_range_i32(1, 100);
            let n = rng.gen_range_usize(1, 20);
            let mut nums: Vec<i32> = Vec::new();
            let mut v = t + 1;
            while nums.len() < n && v <= 1000 {
                nums.push(v);
                v += 1;
            }
            if nums.is_empty() {
                nums.push(1000);
            }
            (nums, t)
        }
        7 => {
            // nums = [1], various targets
            let t = rng.gen_range_i32(1, 30);
            (vec![1], t)
        }
        8 => {
            // powers of 2
            let nums = vec![1, 2, 4, 8, 16, 32, 64, 128, 256, 512];
            let t = rng.gen_range_i32(1, 1000);
            (nums, t)
        }
        9 => {
            // target small, many options
            let n = rng.gen_range_usize(1, 10);
            let nums = make_distinct_nums(rng, n, 10);
            let t = rng.gen_range_i32(1, 10);
            (nums, t)
        }
        _ => {
            // Random case
            let n = rng.gen_range_usize(1, 200);
            let nums = make_distinct_nums(rng, n, 1000);
            let t = rng.gen_range_i32(1, 1000);
            (nums, t)
        }
    }
}

fn validate_and_fix(nums: Vec<i32>, target: i32) -> (Vec<i32>, i32) {
    // Ensure 1 <= len <= 200
    let mut n = nums;
    if n.is_empty() {
        n.push(1);
    }
    if n.len() > 200 {
        n.truncate(200);
    }
    // Clamp values and ensure distinct in [1,1000]
    let mut seen: Vec<i32> = Vec::new();
    let mut next_val: i32 = 1;
    for i in 0..n.len() {
        let mut v = n[i];
        if v < 1 { v = 1; }
        if v > 1000 { v = 1000; }
        let mut dup = false;
        for &u in &seen {
            if u == v { dup = true; break; }
        }
        if dup {
            // find next available
            while next_val <= 1000 {
                let mut d = false;
                for &u in &seen {
                    if u == next_val { d = true; break; }
                }
                if !d { break; }
                next_val += 1;
            }
            v = next_val;
            next_val += 1;
        }
        seen.push(v);
        n[i] = v;
    }
    let mut t = target;
    if t < 1 { t = 1; }
    if t > 1000 { t = 1000; }
    (n, t)
}

fn print_json(nums: &[i32], target: i32) {
    let (nums, target) = generate_test_case(nums.to_vec(), target);
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("],\"target\":{}}}", target);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (nums_raw, tgt_raw) = adversarial_mode(&mut rng, mode);
        let (nums, tgt) = validate_and_fix(nums_raw, tgt_raw);
        let (out_nums, out_tgt) = generate_candidate(&nums, tgt);
        print_json(&out_nums, out_tgt);
    }
}
