use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize) -> (nums: Vec<i32>)
    requires
        3 <= n <= 100_000,
    ensures
        3 <= nums.len() <= 100_000,
        nums.len() == n,
        forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 100_000,
        forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] != nums[j],
{
    let mut nums: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            3 <= n <= 100_000,
            k <= n,
            nums.len() == k,
            forall |i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] == i as i32,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 100_000,
        decreases n - k,
    {
        nums.push(k as i32);
        k = k + 1;
    }

    proof {
        assert forall |i: int, j: int| 0 <= i < j < nums.len() implies nums[i] != nums[j] by {
            assert(nums[i] == i as i32);
            assert(nums[j] == j as i32);
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
        Self { state: seed }
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
}

fn shuffle(v: &mut Vec<i32>, rng: &mut Rng) {
    let n = v.len();
    if n < 2 {
        return;
    }
    let mut i = n - 1;
    while i > 0 {
        let j = rng.gen_range_usize(0, i);
        v.swap(i, j);
        i -= 1;
    }
}

// Produce a distinct-value Vec<i32> of length n, values in [0, 100_000].
fn make_distinct(n: usize, rng: &mut Rng, mode: usize) -> Vec<i32> {
    // Build a pool of distinct candidates then shuffle or choose
    // Our generator uses 0..n which fits since n <= 100_000.
    let mut base: Vec<i32> = (0..(n as i32)).collect();

    match mode {
        0 => {
            // sorted ascending 0..n
            base
        }
        1 => {
            // sorted descending
            base.reverse();
            base
        }
        2 => {
            // pure random shuffle of 0..n
            shuffle(&mut base, rng);
            base
        }
        3 => {
            // alternating small/large - pattern where averages often match
            let mut out: Vec<i32> = Vec::with_capacity(n);
            let mut lo = 0i32;
            let mut hi = (n as i32) - 1;
            let mut toggle = false;
            while out.len() < n {
                if toggle {
                    out.push(hi);
                    hi -= 1;
                } else {
                    out.push(lo);
                    lo += 1;
                }
                toggle = !toggle;
            }
            out
        }
        4 => {
            // Arithmetic progression (equal spacing) - average of neighbors equals self!
            // This is a worst case adversarial input for rearrangement.
            base
        }
        5 => {
            // Two arithmetic progressions interleaved
            let mut out: Vec<i32> = Vec::with_capacity(n);
            let mut i = 0i32;
            while (out.len() as i32) < (n as i32) {
                out.push(i * 2);
                if (out.len() as i32) < (n as i32) {
                    out.push(i * 2 + 1);
                }
                i += 1;
            }
            out
        }
        6 => {
            // Clustered small values: 0..n but then shuffle pairwise
            let mut i = 0;
            while i + 1 < n {
                base.swap(i, i + 1);
                i += 2;
            }
            base
        }
        7 => {
            // Half sorted, half reversed
            let half = n / 2;
            let mut out: Vec<i32> = Vec::with_capacity(n);
            let mut i = 0i32;
            while (i as usize) < half {
                out.push(i);
                i += 1;
            }
            let mut j = (n as i32) - 1;
            while (out.len()) < n {
                out.push(j);
                j -= 1;
            }
            out
        }
        8 => {
            // Large range: map index k to k, but permute via stride
            let stride = 7usize;
            let mut out: Vec<i32> = vec![0; n];
            let mut used = vec![false; n];
            let mut idx = 0usize;
            let mut k = 0usize;
            while k < n {
                while used[idx] {
                    idx = (idx + 1) % n;
                }
                out[idx] = k as i32;
                used[idx] = true;
                idx = (idx + stride) % n;
                k += 1;
            }
            out
        }
        9 => {
            // Randomly pick n distinct values from [0, 100_000] using shuffle of 0..100_001 prefix
            let pool_size: usize = 100_001;
            let mut pool: Vec<i32> = (0..(pool_size as i32)).collect();
            // partial shuffle
            let mut i = 0;
            while i < n {
                let j = rng.gen_range_usize(i, pool_size - 1);
                pool.swap(i, j);
                i += 1;
            }
            pool.truncate(n);
            pool
        }
        _ => {
            shuffle(&mut base, rng);
            base
        }
    }
}

fn print_json(nums: &[i32]) {
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
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n: usize = match mode {
            0 => 3,
            1 => 4,
            2 => 5 + (t % 50),
            3 => 10 + (t % 90),
            4 => 100 + (t % 900),
            5 => 1000 + (t % 500),
            6 => 3 + (t % 20),
            7 => 50 + (t % 200),
            8 => 100,
            9 => 100_000,
            _ => 3 + (t % 10),
        };

        // Build the vec using unverified logic.
        let raw = make_distinct(n, &mut rng, mode);

        // Validate: must be distinct and in range [0, 100_000]. If not, fall back to verified generator.
        let mut ok = true;
        if raw.len() != n {
            ok = false;
        }
        for v in &raw {
            if *v < 0 || *v > 100_000 {
                ok = false;
                break;
            }
        }
        if ok {
            // distinctness check via sort copy
            let mut sorted = raw.clone();
            sorted.sort();
            for i in 1..sorted.len() {
                if sorted[i] == sorted[i - 1] {
                    ok = false;
                    break;
                }
            }
        }

        let nums = if ok {
            raw
        } else {
            generate_test_case(n)
        };

        // Final safety: if somehow still bad, use verified generator
        let nums = if nums.len() >= 3 && nums.len() <= 100_000 {
            nums
        } else {
            generate_test_case(if n < 3 { 3 } else if n > 100_000 { 100_000 } else { n })
        };

        print_json(&nums);
    }
}