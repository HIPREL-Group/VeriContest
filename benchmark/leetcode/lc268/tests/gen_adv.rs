use vstd::prelude::*;

verus! {

pub open spec fn contains_spec(nums: Seq<i32>, value: i32) -> bool {
    exists |j: int| 0 <= j < nums.len() && #[trigger] nums[j] == value
}

// Generate test case where: nums is a permutation of [0..n+1] \ {missing_val}
// Parameters: n = length, missing_val in [0, n], perm = a permutation of {0..n} \ {missing_val}
// We construct by: for i in 0..n, output perm[i].
// Simpler: we take the missing value and a shuffle (as a sequence of the remaining values).
// Requires perm to be length n, all values in [0, n], distinct, none equal to missing_val.

pub fn generate_test_case(
    n: usize,
    missing_val: i32,
    perm: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= n <= 10_000,
        0 <= missing_val <= n as i32,
        perm.len() == n,
        forall |i: int| 0 <= i < perm.len() ==> 0 <= #[trigger] perm[i] <= n as i32,
        forall |i: int| 0 <= i < perm.len() ==> #[trigger] perm[i] != missing_val,
        forall |i: int, j: int| 0 <= i < j < perm.len() ==> perm[i] != perm[j],
    ensures
        1 <= nums.len() <= 10_000,
        forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= nums.len() as i32,
        forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] != nums[j],
        exists |k: int| 0 <= k <= nums.len() && !(#[trigger] contains_spec(nums@, k as i32)),
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            nums.len() == i,
            perm.len() == n,
            1 <= n <= 10_000,
            0 <= missing_val <= n as i32,
            forall |k: int| 0 <= k < i as int ==> #[trigger] nums[k] == perm[k],
            forall |k: int| 0 <= k < perm.len() ==> 0 <= #[trigger] perm[k] <= n as i32,
            forall |k: int| 0 <= k < perm.len() ==> #[trigger] perm[k] != missing_val,
            forall |a: int, b: int| 0 <= a < b < perm.len() ==> perm[a] != perm[b],
        decreases n - i,
    {
        nums.push(perm[i]);
        i = i + 1;
    }

    proof {
        assert(nums.len() == n);
        assert forall |k: int| 0 <= k < nums.len() implies 0 <= #[trigger] nums[k] <= nums.len() as i32 by {
            assert(nums[k] == perm[k]);
        }
        assert forall |a: int, b: int| 0 <= a < b < nums.len() implies nums[a] != nums[b] by {
            assert(nums[a] == perm[a]);
            assert(nums[b] == perm[b]);
        }
        assert(0 <= missing_val as int <= nums.len() as int);
        assert(!contains_spec(nums@, missing_val)) by {
            assert forall |j: int| 0 <= j < nums@.len() implies #[trigger] nums@[j] != missing_val by {
                assert(nums[j] == perm[j]);
            }
        }
        assert(exists |k: int| 0 <= k <= nums.len() && !(#[trigger] contains_spec(nums@, k as i32))) by {
            assert(0 <= missing_val as int <= nums.len() as int);
            assert(!contains_spec(nums@, missing_val as i32));
        }
    }

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
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range(&mut self, lo: usize, hi: usize) -> usize {
        // inclusive
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
}

fn build_perm(n: usize, missing_val: i32, shuffle_seed: u64) -> Vec<i32> {
    // Build [0, 1, ..., n] \ {missing_val} and shuffle
    let mut v: Vec<i32> = Vec::new();
    for i in 0..=n as i32 {
        if i != missing_val {
            v.push(i);
        }
    }
    // Fisher-Yates shuffle
    let mut rng = Rng::new(shuffle_seed);
    let len = v.len();
    if len > 1 {
        for i in (1..len).rev() {
            let j = rng.gen_range(0, i);
            v.swap(i, j);
        }
    }
    v
}

fn print_json(nums: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("]}}");
}

fn make_case(n: usize, missing_val: i32, shuffle_seed: u64) {
    let perm = build_perm(n, missing_val, shuffle_seed);
    let nums = generate_test_case(n, missing_val, &perm);
    print_json(&nums);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };
    let mut rng = Rng::new(seed);

    let total = 220usize;
    for t in 0..total {
        let mode = t % 11;
        let (n, missing_val): (usize, i32) = match mode {
            0 => (1, 0),
            1 => (1, 1),
            2 => (2, 0),
            3 => (2, 2),
            4 => {
                let n = rng.gen_range(1, 20);
                (n, 0)
            }
            5 => {
                let n = rng.gen_range(1, 20);
                (n, n as i32)
            }
            6 => {
                let n = rng.gen_range(1, 100);
                let m = rng.gen_range(0, n) as i32;
                (n, m)
            }
            7 => (10_000, 0),
            8 => (10_000, 10_000),
            9 => (10_000, 5000),
            10 => {
                let n = rng.gen_range(1, 10_000);
                let m = rng.gen_range(0, n) as i32;
                (n, m)
            }
            _ => (3, 2),
        };
        make_case(n, missing_val, rng.next_u64());
    }
}