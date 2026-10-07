use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    len_half: usize,
    fillers: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= len_half <= 50,
        fillers.len() == 2 * len_half,
        forall|i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 100,
    ensures
        2 <= nums.len() <= 100,
        nums.len() % 2 == 0,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
{
    let n: usize = 2 * len_half;
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == 2 * len_half,
            1 <= len_half <= 50,
            fillers.len() == n,
            0 <= i <= n,
            nums.len() == i,
            forall|k: int| 0 <= k < fillers.len() ==> 1 <= #[trigger] fillers[k] <= 100,
            forall|k: int| 0 <= k < i as int ==> #[trigger] nums[k] == fillers[k],
            forall|k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 100,
        decreases n - i,
    {
        nums.push(fillers[i]);
        i = i + 1;
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

fn build_fillers(vals: Vec<i32>) -> Vec<i32> {
    // Clamp to [1,100]
    let mut out = Vec::with_capacity(vals.len());
    for v in vals {
        let mut x = v;
        if x < 1 { x = 1; }
        if x > 100 { x = 100; }
        out.push(x);
    }
    out
}

fn gen_mode(rng: &mut Rng, mode: usize) -> (usize, Vec<i32>) {
    // returns (len_half, fillers)
    let len_half: usize = match mode {
        0 => 1, // minimum size = 2
        1 => 50, // maximum size = 100
        2 => rng.gen_range_usize(1, 50),
        3 => 2,
        4 => 3,
        5 => rng.gen_range_usize(1, 10),
        6 => 50,
        7 => rng.gen_range_usize(1, 50),
        8 => rng.gen_range_usize(1, 50),
        9 => rng.gen_range_usize(1, 50),
        _ => rng.gen_range_usize(1, 50),
    };
    let n = 2 * len_half;
    let mut fillers: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 | 3 | 4 => {
            // random small
            for _ in 0..n {
                fillers.push(rng.gen_range_usize(1, 100) as i32);
            }
        }
        1 => {
            // all same value
            let v = rng.gen_range_usize(1, 100) as i32;
            for _ in 0..n {
                fillers.push(v);
            }
        }
        2 => {
            // all 1s
            for _ in 0..n {
                fillers.push(1);
            }
        }
        5 => {
            // all 100s
            for _ in 0..n {
                fillers.push(100);
            }
        }
        6 => {
            // sorted ascending
            for i in 0..n {
                let v = ((i % 100) + 1) as i32;
                fillers.push(v);
            }
        }
        7 => {
            // sorted descending
            for i in 0..n {
                let v = (100 - (i % 100)) as i32;
                fillers.push(v);
            }
        }
        8 => {
            // many duplicates, pairs
            for i in 0..n {
                let v = ((i / 2) % 100 + 1) as i32;
                fillers.push(v);
            }
        }
        9 => {
            // alternating 1 and 100
            for i in 0..n {
                fillers.push(if i % 2 == 0 { 1 } else { 100 });
            }
        }
        _ => {
            for _ in 0..n {
                fillers.push(rng.gen_range_usize(1, 100) as i32);
            }
        }
    }
    (len_half, build_fillers(fillers))
}

fn print_json(nums: &[i32], value: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("],\"value\":{}}}", value);
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
        let (len_half, fillers) = gen_mode(&mut rng, mode);
        let value = if fillers.is_empty() { 1 } else { fillers[0] };
        let nums = generate_test_case(len_half, &fillers);
        print_json(&nums, value);
    }
}