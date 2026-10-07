use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    peak: usize,
) -> (nums: Vec<i32>)
    requires
        3 <= n <= 1000,
        1 <= peak < n - 1,
    ensures
        3 <= nums.len() <= 1000,
        nums.len() == n,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000i32,
        exists |a: int, b: int, c: int| 0 <= a < b < c < nums.len() as int
            && nums[a] < nums[b] && nums[b] > nums[c],
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;

    // Use the simple pattern 1, ..., 1, 2 at `peak`, 1, ..., 1.
    // Since 1 <= peak < n - 1, the triple (0, peak, peak + 1) always witnesses a mountain.

    while i < n
        invariant
            3 <= n <= 1000,
            1 <= peak < n - 1,
            0 <= i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < i as int ==>
                #[trigger] nums[k] == if k == peak as int { 2i32 } else { 1i32 },
        decreases n - i,
    {
        if i == peak {
            nums.push(2i32);
        } else {
            nums.push(1i32);
        }
        i = i + 1;
    }

    proof {
        assert forall |k: int| 0 <= k < nums.len() implies 1 <= #[trigger] nums[k] <= 1_000_000_000i32
        by {
            if k == peak as int {
                assert(nums[k] == 2i32);
                assert(1 <= 2i32 <= 1_000_000_000i32);
            } else {
                assert(nums[k] == 1i32);
                assert(1 <= 1i32 <= 1_000_000_000i32);
            }
        }

        let a: int = 0;
        let b: int = peak as int;
        let c: int = peak as int + 1;
        assert(0 <= a < b < c < nums.len() as int);
        assert(nums[a] == 1i32);
        assert(nums[b] == 2i32);
        assert(nums[c] == 1i32);
        assert(nums[a] < nums[b]);
        assert(nums[b] > nums[c]);
        assert(exists |a: int, b: int, c: int| 0 <= a < b < c < nums.len() as int
            && nums[a] < nums[b] && nums[b] > nums[c]);
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
        assert!(lo <= hi);
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
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

fn pick_n_peak(rng: &mut Rng, mode: usize, t: usize) -> (usize, usize) {
    match mode {
        0 => (3, 1),
        1 => (4, 1),
        2 => (4, 2),
        3 => (1000, 1),
        4 => (1000, 998),
        5 => (1000, 500),
        6 => {
            let n = rng.gen_range_usize(3, 10);
            let peak = rng.gen_range_usize(1, n - 2);
            (n, peak)
        }
        7 => {
            let n = rng.gen_range_usize(50, 200);
            let peak = rng.gen_range_usize(1, n - 2);
            (n, peak)
        }
        8 => {
            let n = rng.gen_range_usize(500, 1000);
            let peak = rng.gen_range_usize(1, n - 2);
            (n, peak)
        }
        9 => {
            let n = rng.gen_range_usize(3, 1000);
            let peak = 1usize;
            (n, peak)
        }
        _ => {
            let n = 3 + (t % 998);
            let peak = 1 + (t % (n - 2));
            (n, peak)
        }
    }
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

    for t in 0..total {
        let mode = t % modes;
        let (n, peak) = pick_n_peak(&mut rng, mode, t);
        let nums = generate_test_case(n, peak);
        print_json(&nums);
    }
}
