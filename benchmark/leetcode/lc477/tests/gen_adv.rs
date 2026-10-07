use vstd::prelude::*;

verus! {

pub open spec fn bit_limit(k: nat) -> nat
    decreases k,
{
    if k == 0 { 1 } else { 2 * bit_limit((k - 1) as nat) }
}
proof fn popcount_bound(x: nat, acc: nat, bits: nat)
    requires x < bit_limit(bits),
    ensures hamming_distance_spec_helper(x, acc) <= acc + bits,
    decreases bits,
{
    if x > 0 {
        assert(bits > 0);
        assert(x / 2 < bit_limit((bits - 1) as nat)) by(nonlinear_arith)
            requires x < 2 * bit_limit((bits - 1) as nat);
        popcount_bound(x / 2, acc + x % 2, (bits - 1) as nat);
    }
}
proof fn total_distance_bound(nums: Seq<i32>, i: nat, j: nat, acc: nat)
    requires nums.len() <= 10000, i <= nums.len(), i + 1 <= j <= nums.len() + 1,
        i < nums.len() ==> j <= nums.len(),
        forall|k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] <= 1000000000,
    ensures total_hamming_distance_spec(nums, i, j, acc) <=
        acc + 16 * (nums.len() - i - 1) * (nums.len() - i - 2) + 32 * (nums.len() - j),
    decreases nums.len() - i, nums.len() - j,
{
    let n = nums.len() as int;
    if i >= nums.len() {
        assert(16 * (n - i - 1) * (n - i - 2) + 32 * (n - j) == 0) by(nonlinear_arith)
            requires i == n, j == n + 1;
    } else if j >= nums.len() {
        total_distance_bound(nums, i + 1, i + 2, acc);
        assert(16 * (n - (i + 1) - 1) * (n - (i + 1) - 2) + 32 * (n - (i + 2))
            <= 16 * (n - i - 1) * (n - i - 2) + 32 * (n - j)) by(nonlinear_arith)
            requires j == n;
    } else {
        let a = nums[i as int]; let b = nums[j as int];
        assert(0 <= (a ^ b) <= 2147483647) by(bit_vector)
            requires 0 <= a <= 1000000000, 0 <= b <= 1000000000;
        reveal_with_fuel(bit_limit, 32);
        popcount_bound((a ^ b) as nat, 0, 31);
        let dist = hamming_distance_spec((a ^ b) as nat);
        total_distance_bound(nums, i, j + 1, acc + dist);
    }
}
pub fn generate_test_case(raw: Vec<i32>) -> (result: Vec<i32>)
    ensures 1 <= result.len() <= 10000,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 1000000000,
        i32::MIN <= total_hamming_distance_spec(result@, 0, 1, 0) <= i32::MAX,
{
    let n = if raw.len() == 0 { 1usize } else if raw.len() > 10000 { 10000usize } else { raw.len() };
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant i <= n, 1 <= n <= 10000, result.len() == i,
            forall|j: int| 0 <= j < i ==> 0 <= #[trigger] result[j] <= 1000000000,
        decreases n - i,
    {
        let v = if i < raw.len() { raw[i] } else { 0 };
        result.push(if v < 0 { 0 } else if v > 1000000000 { 1000000000 } else { v });
        i += 1;
    }
    proof {
        total_distance_bound(result@, 0, 1, 0);
        assert(16 * (n - 1) * (n - 2) + 32 * (n - 1) <= 2147483647) by(nonlinear_arith)
            requires 1 <= n <= 10000;
    }
    result
}


pub open spec fn hamming_distance_spec_helper(x: nat, acc: nat) -> nat
    decreases x,
{
    if x == 0 {
        acc
    } else {
        let ones = x % 2;
        let new_acc = acc + ones;
        hamming_distance_spec_helper(x / 2, new_acc)
    }
}

pub open spec fn hamming_distance_spec(xor_result: nat) -> nat {
    hamming_distance_spec_helper(xor_result, 0)
}

pub open spec fn total_hamming_distance_spec(nums: Seq<i32>, i: nat, j: nat, acc: nat) -> nat
    decreases nums.len() - i, nums.len() - j,
{
    if i >= nums.len() {
        acc
    } else if j >= nums.len() {
        total_hamming_distance_spec(nums, i + 1, i + 2, acc)
    } else {
        let xor_val = (nums[i as int] ^ nums[j as int]) as nat;
        let dist = hamming_distance_spec(xor_val);
        total_hamming_distance_spec(nums, i, j + 1, acc + dist)
    }
}

// Generator: build a Vec<i32> from the provided values, ensuring all elements are
// in [0, i32::MAX]. The caller is trusted (via requires) to pass in values whose
// total hamming distance fits in i32.
pub fn generate_candidate(
    vals: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= vals.len() <= 10000,
        forall|i: int| 0 <= i < vals.len() ==> 0 <= #[trigger] vals[i] <= i32::MAX,
        i32::MIN <= total_hamming_distance_spec(vals@, 0, 1, 0) <= i32::MAX,
    ensures
        1 <= nums.len() <= 10000,
        forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= i32::MAX,
        i32::MIN <= total_hamming_distance_spec(nums@, 0, 1, 0) <= i32::MAX,
        nums@ == vals@,
{
    let mut nums: Vec<i32> = Vec::new();
    let n = vals.len();
    let mut k: usize = 0;
    while k < n
        invariant
            n == vals.len(),
            0 <= k <= n,
            nums.len() == k,
            forall|i: int| 0 <= i < k as int ==> nums[i] == vals[i],
        decreases n - k,
    {
        nums.push(vals[k]);
        k = k + 1;
    }
    assert(nums@ =~= vals@);
    nums
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
        self.state = self
            .state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_i32_pos(&mut self, hi: i32) -> i32 {
        let span = (hi as u64) + 1;
        (self.next_u64() % span) as i32
    }
}

// Compute hamming distance between two non-negative i32 values.
fn hamming(a: i32, b: i32) -> u64 {
    let mut x = (a ^ b) as u32;
    let mut c: u64 = 0;
    while x != 0 {
        c += (x & 1) as u64;
        x >>= 1;
    }
    c
}

// Total hamming distance sum; returns None if overflows i32.
fn total_hd_check(nums: &[i32]) -> Option<i64> {
    let n = nums.len();
    let mut sum: i64 = 0;
    for i in 0..n {
        for j in (i + 1)..n {
            sum += hamming(nums[i], nums[j]) as i64;
            if sum > i32::MAX as i64 {
                return None;
            }
        }
    }
    Some(sum)
}

fn build_mode(rng: &mut Rng, mode: usize, idx: usize) -> Vec<i32> {
    match mode {
        0 => {
            // Single element
            let v = rng.gen_i32_pos(i32::MAX);
            vec![v]
        }
        1 => {
            // Two elements
            let a = rng.gen_i32_pos(i32::MAX);
            let b = rng.gen_i32_pos(i32::MAX);
            vec![a, b]
        }
        2 => {
            // All zeros
            let n = rng.gen_range_usize(1, 100);
            vec![0i32; n]
        }
        3 => {
            // All same value
            let n = rng.gen_range_usize(1, 100);
            let v = rng.gen_i32_pos(i32::MAX);
            vec![v; n]
        }
        4 => {
            // Alternating 0 and 1
            let n = rng.gen_range_usize(2, 200);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push((i & 1) as i32);
            }
            v
        }
        5 => {
            // Powers of two
            let n = rng.gen_range_usize(2, 31);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push(1i32 << (i % 30));
            }
            v
        }
        6 => {
            // Small random values
            let n = rng.gen_range_usize(2, 50);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_i32_pos(15));
            }
            v
        }
        7 => {
            // Edge: values near i32::MAX
            let n = rng.gen_range_usize(2, 30);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                let high = i32::MAX - rng.gen_i32_pos(1000);
                v.push(high);
            }
            v
        }
        8 => {
            // Random up to 10^9
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_i32_pos(1_000_000_000));
            }
            v
        }
        9 => {
            // Example from problem
            if idx % 2 == 0 {
                vec![4, 14, 2]
            } else {
                vec![4, 14, 4]
            }
        }
        _ => {
            // Mixed random
            let n = rng.gen_range_usize(1, 200);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_i32_pos(i32::MAX));
            }
            v
        }
    }
}

fn print_json(nums: &[i32]) {
    let nums = generate_test_case(nums.to_vec());
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", nums[i]);
    }
    println!("]}}");
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
    let total = 220usize;
    let mut emitted = 0usize;
    let mut attempts = 0usize;
    while emitted < total && attempts < total * 4 {
        attempts += 1;
        let mode = attempts % modes;
        let candidate = build_mode(&mut rng, mode, emitted);
        if candidate.is_empty() || candidate.len() > 10000 {
            continue;
        }
        // Ensure all values non-negative in [0, i32::MAX]
        let mut ok = true;
        for &v in &candidate {
            if v < 0 {
                ok = false;
                break;
            }
        }
        if !ok {
            continue;
        }
        // Check total hamming distance fits in i32.
        match total_hd_check(&candidate) {
            Some(_) => {
                let vals = candidate.clone();
                let nums = generate_candidate(&vals);
                print_json(&nums);
                emitted += 1;
            }
            None => {
                // Skip if overflow
                continue;
            }
        }
    }
}
