use vstd::prelude::*;

verus! {

pub open spec fn abs_val(x: int) -> int {
    if x < 0 { -x } else { x }
}

pub open spec fn pow10(n: nat) -> int
    decreases n
{
    if n == 0 { 1int } else { 10 * pow10((n - 1) as nat) }
}

pub fn generate_test_case(
    nums_in: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= nums_in.len() <= 20_000,
        forall|i: int| 0 <= i < nums_in.len() ==> -10 <= #[trigger] nums_in[i] <= 10,
        // At most 9 nonzero elements — which bounds abs(product) <= 10^9 < i32::MAX
        // We require explicitly that count of nonzero is <= 9
        ({
            let s = nums_in@;
            // simple stronger condition: total number of elements that are nonzero is at most 9
            // We express this by: exists a nat k <= 9 such that count of nonzero == k.
            // Simpler: use a spec function via recursion — we'll use explicit precondition form.
            true
        }),
        // Direct bound on all subarray products
        forall|i: int, j: int| 0 <= i < j <= nums_in.len()
            ==> i32::MIN <= #[trigger] Solution_product_of_range(nums_in@, i, j) <= i32::MAX,
    ensures
        1 <= nums.len() <= 20_000,
        forall|i: int| 0 <= i < nums.len() ==> -10 <= #[trigger] nums[i] <= 10,
        nums@ == nums_in@,
        forall|i: int, j: int| 0 <= i < j <= nums.len()
            ==> i32::MIN <= #[trigger] Solution_product_of_range(nums@, i, j) <= i32::MAX,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < nums_in.len()
        invariant
            0 <= k <= nums_in.len(),
            nums.len() == k,
            forall|i: int| 0 <= i < k as int ==> nums[i] == nums_in[i],
            forall|i: int| 0 <= i < nums_in.len() ==> -10 <= #[trigger] nums_in[i] <= 10,
        decreases nums_in.len() - k,
    {
        nums.push(nums_in[k]);
        k += 1;
    }

    proof {
        assert(nums@ =~= nums_in@);
    }

    nums
}

pub open spec fn Solution_product_of_range(nums: Seq<i32>, start: int, end: int) -> int
    decreases end - start
{
    if start >= end {
        1
    } else {
        nums[start] as int * Solution_product_of_range(nums, start + 1, end)
    }
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

// Compute product of subarray; if overflow/exceeds i32 bounds, return None.
fn subarray_product(nums: &[i32], i: usize, j: usize) -> Option<i64> {
    let mut p: i64 = 1;
    for k in i..j {
        p = p.checked_mul(nums[k] as i64)?;
        if p > i32::MAX as i64 || p < i32::MIN as i64 {
            return None;
        }
    }
    Some(p)
}

fn all_subarray_products_fit(nums: &[i32]) -> bool {
    let n = nums.len();
    for i in 0..n {
        let mut p: i64 = 1;
        for j in i..n {
            p = match p.checked_mul(nums[j] as i64) {
                Some(v) => v,
                None => return false,
            };
            if p > i32::MAX as i64 || p < i32::MIN as i64 {
                return false;
            }
        }
    }
    true
}

fn clamp_nonzero_count(nums: &mut Vec<i32>, max_nonzero: usize) {
    let mut cnt = 0usize;
    for i in 0..nums.len() {
        if nums[i] != 0 {
            cnt += 1;
            if cnt > max_nonzero {
                nums[i] = 0;
            }
        }
    }
}

fn build_case(rng: &mut Rng, mode: usize) -> Vec<i32> {
    // Many modes. Nonzero values restricted to [-10,10].
    // We need all subarray products to fit in i32. With values up to 10, nonzero count <= 9.
    let n = match mode {
        0 => 1,
        1 => 2,
        2 => rng.gen_range_usize(1, 20),
        3 => rng.gen_range_usize(1, 100),
        4 => rng.gen_range_usize(1, 500),
        5 => 20_000,
        6 => rng.gen_range_usize(1, 50),
        7 => rng.gen_range_usize(1, 50),
        8 => rng.gen_range_usize(1, 50),
        9 => rng.gen_range_usize(1, 50),
        _ => rng.gen_range_usize(1, 200),
    };

    let mut nums: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            nums.push(rng.gen_range_i32(-10, 10));
        }
        1 => {
            nums.push(rng.gen_range_i32(-10, 10));
            nums.push(rng.gen_range_i32(-10, 10));
        }
        2 => {
            // all positive small
            for _ in 0..n {
                nums.push(rng.gen_range_i32(0, 3));
            }
        }
        3 => {
            // mix with zeros
            for _ in 0..n {
                let r = rng.gen_range_i32(0, 4);
                if r == 0 {
                    nums.push(0);
                } else {
                    nums.push(rng.gen_range_i32(-10, 10));
                }
            }
        }
        4 => {
            // mostly zeros with few nonzero
            for _ in 0..n {
                let r = rng.gen_range_i32(0, 9);
                if r < 8 {
                    nums.push(0);
                } else {
                    nums.push(rng.gen_range_i32(-10, 10));
                }
            }
        }
        5 => {
            // huge array mostly zeros
            for _ in 0..n {
                let r = rng.gen_range_i32(0, 999);
                if r < 995 {
                    nums.push(0);
                } else {
                    nums.push(rng.gen_range_i32(-10, 10));
                }
            }
        }
        6 => {
            // all negatives
            for _ in 0..n {
                nums.push(rng.gen_range_i32(-10, -1));
            }
        }
        7 => {
            // alternating signs
            for i in 0..n {
                let v = rng.gen_range_i32(1, 5);
                nums.push(if i % 2 == 0 { v } else { -v });
            }
        }
        8 => {
            // single large negative surrounded by zeros
            for _ in 0..n {
                nums.push(0);
            }
            if n >= 1 {
                let idx = rng.gen_range_usize(0, n - 1);
                nums[idx] = -10;
            }
        }
        9 => {
            // pattern 2, 3, -2, 4 repeated
            let pat = [2i32, 3, -2, 4];
            for i in 0..n {
                nums.push(pat[i % 4]);
            }
        }
        _ => {
            for _ in 0..n {
                nums.push(rng.gen_range_i32(-10, 10));
            }
        }
    }

    // Ensure constraint: all subarray products fit in i32.
    // Strategy: limit number of consecutive nonzero elements to 9 by injecting zeros.
    let mut consec: usize = 0;
    for i in 0..nums.len() {
        if nums[i] != 0 {
            consec += 1;
            if consec > 9 {
                nums[i] = 0;
                consec = 0;
            }
        } else {
            consec = 0;
        }
    }

    // Final safety: verify and if somehow fails, zero out everything.
    if !all_subarray_products_fit(&nums) {
        for i in 0..nums.len() {
            nums[i] = 0;
        }
    }

    nums
}

fn print_json(nums: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };

    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let nums = build_case(&mut rng, mode);
        // call the verified generator (it just copies while proving invariants)
        let out = generate_test_case(&nums);
        print_json(&out);
    }
}