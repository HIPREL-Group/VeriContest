use vstd::prelude::*;

verus! {

/// Constructs a valid `Vec<i32>` for min_operations from seed elements,
/// applying mutation_kind to diversify the generated inputs.
///
/// Mutations:
///   0 — identity (copy seed elements as-is)
///   1 — set all elements to 1 (min boundary)
///   2 — set all elements to 1_000_000_000 (max boundary)
///   3 — nudge first element up: if < 1_000_000_000, increment by 1
///   4 — nudge first element down: if > 1, decrement by 1
///   5 — set last element to 1 (min boundary element)
///   6 — set last element to 1_000_000_000 (max boundary element)
///   7 — swap first and last elements
pub fn generate_test_case(
    seed_nums: Vec<i32>,
    k: i32,
    mutation_kind: u8,
) -> (nums: Vec<i32>)
    requires
        2 <= seed_nums.len() <= 200_000,
        forall |i: int| 0 <= i < seed_nums.len() ==> 1 <= #[trigger] seed_nums[i] <= 1_000_000_000,
        1 <= k <= 1_000_000_000,
    ensures
        2 <= nums.len() <= 200_000,
        1 <= k <= 1_000_000_000,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
{
    let n = seed_nums.len();
    if mutation_kind == 1 {
        let mut out: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == seed_nums.len(),
                2 <= n <= 200_000,
                out.len() == j,
                forall |idx: int| 0 <= idx < j ==> #[trigger] out[idx] == 1i32,
                forall |idx: int| 0 <= idx < j ==> 1 <= #[trigger] out[idx] <= 1_000_000_000,
            decreases n - j,
        {
            out.push(1);
            j = j + 1;
        }
        out
    } else if mutation_kind == 2 {
        let mut out: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == seed_nums.len(),
                2 <= n <= 200_000,
                out.len() == j,
                forall |idx: int| 0 <= idx < j ==> #[trigger] out[idx] == 1_000_000_000i32,
                forall |idx: int| 0 <= idx < j ==> 1 <= #[trigger] out[idx] <= 1_000_000_000,
            decreases n - j,
        {
            out.push(1_000_000_000);
            j = j + 1;
        }
        out
    } else if mutation_kind == 3 {
        let mut out: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == seed_nums.len(),
                2 <= n <= 200_000,
                out.len() == j,
                forall |i: int| 0 <= i < seed_nums.len() ==> 1 <= #[trigger] seed_nums[i] <= 1_000_000_000,
                forall |idx: int| 0 <= idx < j ==> 1 <= #[trigger] out[idx] <= 1_000_000_000,
            decreases n - j,
        {
            if j == 0 && seed_nums[0] < 1_000_000_000 {
                out.push(seed_nums[0] + 1);
            } else {
                out.push(seed_nums[j]);
            }
            j = j + 1;
        }
        out
    } else if mutation_kind == 4 {
        let mut out: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == seed_nums.len(),
                2 <= n <= 200_000,
                out.len() == j,
                forall |i: int| 0 <= i < seed_nums.len() ==> 1 <= #[trigger] seed_nums[i] <= 1_000_000_000,
                forall |idx: int| 0 <= idx < j ==> 1 <= #[trigger] out[idx] <= 1_000_000_000,
            decreases n - j,
        {
            if j == 0 && seed_nums[0] > 1 {
                out.push(seed_nums[0] - 1);
            } else {
                out.push(seed_nums[j]);
            }
            j = j + 1;
        }
        out
    } else if mutation_kind == 5 {
        let mut out: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == seed_nums.len(),
                2 <= n <= 200_000,
                out.len() == j,
                forall |i: int| 0 <= i < seed_nums.len() ==> 1 <= #[trigger] seed_nums[i] <= 1_000_000_000,
                forall |idx: int| 0 <= idx < j ==> 1 <= #[trigger] out[idx] <= 1_000_000_000,
            decreases n - j,
        {
            if j == n - 1 {
                out.push(1);
            } else {
                out.push(seed_nums[j]);
            }
            j = j + 1;
        }
        out
    } else if mutation_kind == 6 {
        let mut out: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == seed_nums.len(),
                2 <= n <= 200_000,
                out.len() == j,
                forall |i: int| 0 <= i < seed_nums.len() ==> 1 <= #[trigger] seed_nums[i] <= 1_000_000_000,
                forall |idx: int| 0 <= idx < j ==> 1 <= #[trigger] out[idx] <= 1_000_000_000,
            decreases n - j,
        {
            if j == n - 1 {
                out.push(1_000_000_000);
            } else {
                out.push(seed_nums[j]);
            }
            j = j + 1;
        }
        out
    } else if mutation_kind == 7 {
        let mut out: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == seed_nums.len(),
                2 <= n <= 200_000,
                out.len() == j,
                forall |i: int| 0 <= i < seed_nums.len() ==> 1 <= #[trigger] seed_nums[i] <= 1_000_000_000,
                forall |idx: int| 0 <= idx < j ==> 1 <= #[trigger] out[idx] <= 1_000_000_000,
            decreases n - j,
        {
            if j == 0 {
                out.push(seed_nums[n - 1]);
            } else if j == n - 1 {
                out.push(seed_nums[0]);
            } else {
                out.push(seed_nums[j]);
            }
            j = j + 1;
        }
        out
    } else {
        let mut out: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == seed_nums.len(),
                2 <= n <= 200_000,
                out.len() == j,
                forall |i: int| 0 <= i < seed_nums.len() ==> 1 <= #[trigger] seed_nums[i] <= 1_000_000_000,
                forall |idx: int| 0 <= idx < j ==> 1 <= #[trigger] out[idx] <= 1_000_000_000,
            decreases n - j,
        {
            out.push(seed_nums[j]);
            j = j + 1;
        }
        out
    }
}

} // verus!

struct Rng { state: u64 }

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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build_nums(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            for _ in 0..n { v.push(rng.gen_range_i32(1, 1_000_000_000)); }
        }
        1 => {
            for i in 0..n { v.push(((i as i32) % 1_000_000_000) + 1); }
        }
        2 => {
            for i in 0..n {
                let x = ((n - i) as i32).max(1);
                v.push(if x > 1_000_000_000 { 1_000_000_000 } else { x });
            }
        }
        3 => {
            for _ in 0..n { v.push(1); }
        }
        4 => {
            for _ in 0..n { v.push(1_000_000_000); }
        }
        5 => {
            for i in 0..n {
                v.push(if i % 2 == 0 { 1 } else { 1_000_000_000 });
            }
        }
        6 => {
            for _ in 0..n { v.push(rng.gen_range_i32(1, 10)); }
        }
        7 => {
            for _ in 0..n { v.push(rng.gen_range_i32(999_999_990, 1_000_000_000)); }
        }
        8 => {
            for i in 0..n {
                let x = ((i as i64) * 7919 % 1_000_000_000 + 1) as i32;
                v.push(x);
            }
        }
        9 => {
            for _ in 0..n { v.push(rng.gen_range_i32(1, 1000)); }
        }
        _ => {
            for _ in 0..n {
                let lo = rng.gen_range_i32(1, 100);
                v.push(lo);
            }
        }
    }
    v
}

fn pick_k(rng: &mut Rng, mode: usize) -> i32 {
    match mode {
        0 => rng.gen_range_i32(1, 1_000_000_000),
        1 => 1,
        2 => 1_000_000_000,
        3 => rng.gen_range_i32(1, 100),
        4 => rng.gen_range_i32(500_000_000, 1_000_000_000),
        5 => 2,
        6 => rng.gen_range_i32(1, 10),
        7 => rng.gen_range_i32(1, 1_000_000_000),
        8 => rng.gen_range_i32(1, 1000),
        9 => 999_999_999,
        _ => rng.gen_range_i32(1, 1_000_000),
    }
}

fn print_json(nums: &[i32], k: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("],\"k\":{}}}", k);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(3066)
    } else { 3066 };

    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 100usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => rng.gen_range_usize(2, 50),
            1 => 2,
            2 => 3,
            3 => rng.gen_range_usize(2, 20),
            4 => 100,
            5 => 1000,
            6 => rng.gen_range_usize(2, 10),
            7 => 64,
            8 => rng.gen_range_usize(2, 200),
            9 => 500,
            _ => rng.gen_range_usize(2, 100),
        };
        let n = if n < 2 { 2 } else if n > 200_000 { 200_000 } else { n };

        let seed_nums = build_nums(&mut rng, mode, n);
        let k = pick_k(&mut rng, mode);
        let mutation_kind = ((t / modes) % 8) as u8;
        let nums = generate_test_case(seed_nums, k, mutation_kind);
        print_json(&nums, k);
    }
}
