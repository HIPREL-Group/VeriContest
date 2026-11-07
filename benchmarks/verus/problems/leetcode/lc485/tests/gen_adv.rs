use vstd::prelude::*;

verus! {

pub fn generate_test_case(bits: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= bits.len() <= 100_000,
        forall|i: int| 0 <= i < bits.len() ==> (#[trigger] bits[i]) == 0 || bits[i] == 1,
    ensures
        1 <= nums.len() <= 100_000,
        forall|i: int| 0 <= i < nums.len() ==> (#[trigger] nums[i]) == 0 || nums[i] == 1,
        nums.len() == bits.len(),
        forall|i: int| 0 <= i < nums.len() ==> nums[i] == bits[i],
{
    let n = bits.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            n == bits.len(),
            1 <= n <= 100_000,
            0 <= k <= n,
            nums.len() == k,
            forall|i: int| 0 <= i < bits.len() ==> (#[trigger] bits[i]) == 0 || bits[i] == 1,
            forall|i: int| 0 <= i < k as int ==> (#[trigger] nums[i]) == bits[i],
        decreases n - k,
    {
        let v = bits[k];
        nums.push(v);
        k = k + 1;
    }
    nums
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: if seed == 0 { 1 } else { seed } }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }

    fn gen_bit(&mut self) -> i32 {
        (self.next_u64() & 1) as i32
    }
}

fn all_ones(n: usize) -> Vec<i32> {
    vec![1; n]
}
fn all_zeros(n: usize) -> Vec<i32> {
    vec![0; n]
}

fn alternating(n: usize, start: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        v.push(if (i as i32 + start) % 2 == 0 { 1 } else { 0 });
    }
    v
}

fn one_zero_in_middle(n: usize) -> Vec<i32> {
    let mut v = vec![1; n];
    if n > 0 {
        v[n / 2] = 0;
    }
    v
}

fn ends_with_run(n: usize, run: usize) -> Vec<i32> {
    let mut v = vec![0; n];
    let start = if n >= run { n - run } else { 0 };
    for i in start..n {
        v[i] = 1;
    }
    v
}

fn starts_with_run(n: usize, run: usize) -> Vec<i32> {
    let mut v = vec![0; n];
    let end = if run <= n { run } else { n };
    for i in 0..end {
        v[i] = 1;
    }
    v
}

fn two_equal_runs(n: usize) -> Vec<i32> {
    // runs of length k separated by a zero
    let mut v = vec![0; n];
    if n >= 3 {
        let k = (n - 1) / 2;
        for i in 0..k {
            v[i] = 1;
        }
        for i in (k + 1)..(k + 1 + k).min(n) {
            v[i] = 1;
        }
    } else if n >= 1 {
        v[0] = 1;
    }
    v
}

fn random_bits(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_bit());
    }
    v
}

fn biased_ones(rng: &mut Rng, n: usize, threshold: u64) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        let r = rng.next_u64() % 100;
        v.push(if r < threshold { 1 } else { 0 });
    }
    v
}

fn single_zero_at(n: usize, pos: usize) -> Vec<i32> {
    let mut v = vec![1; n];
    if pos < n {
        v[pos] = 0;
    }
    v
}

fn build_for_mode(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    match mode {
        0 => all_ones(n),
        1 => all_zeros(n),
        2 => alternating(n, 0),
        3 => alternating(n, 1),
        4 => one_zero_in_middle(n),
        5 => ends_with_run(n, n / 2),
        6 => starts_with_run(n, n / 2),
        7 => two_equal_runs(n),
        8 => random_bits(rng, n),
        9 => biased_ones(rng, n, 80),
        10 => biased_ones(rng, n, 20),
        _ => {
            let pos = rng.gen_range_usize(0, n - 1);
            single_zero_at(n, pos)
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
    let modes = 12usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match t % 10 {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => 10,
            4 => 100,
            5 => 1000,
            6 => 10_000,
            7 => 100_000,
            8 => rng.gen_range_usize(1, 500),
            _ => rng.gen_range_usize(1, 5000),
        };
        let bits = build_for_mode(&mut rng, mode, n);
        let nums = generate_test_case(&bits);
        print_json(&nums);
    }
}