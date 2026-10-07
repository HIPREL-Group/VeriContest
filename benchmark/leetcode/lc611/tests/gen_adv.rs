use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 1000,
        forall|i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 1000,
    ensures
        1 <= nums.len() <= 1000,
        forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1000,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            nums.len() == i,
            forall|k: int| 0 <= k < i as int ==> 0 <= #[trigger] nums[k] <= 1000,
            forall|k: int| 0 <= k < i as int ==> nums[k] == values[k],
            forall|k: int| 0 <= k < values.len() ==> 0 <= #[trigger] values[k] <= 1000,
        decreases n - i,
    {
        nums.push(values[i]);
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
        lo + ((self.next_u64() % span) as i32)
    }
}

fn gen_mode(rng: &mut Rng, mode: usize) -> Vec<i32> {
    match mode {
        0 => {
            // Small random
            let n = rng.gen_range_usize(1, 10);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 20));
            }
            v
        }
        1 => {
            // Single element
            vec![rng.gen_range_i32(0, 1000)]
        }
        2 => {
            // All zeros
            let n = rng.gen_range_usize(3, 50);
            vec![0i32; n]
        }
        3 => {
            // All same non-zero
            let n = rng.gen_range_usize(3, 100);
            let v = rng.gen_range_i32(1, 1000);
            vec![v; n]
        }
        4 => {
            // Fibonacci-like (edge: no triangles)
            let n = rng.gen_range_usize(3, 20);
            let mut v = vec![1i32, 1i32];
            while v.len() < n {
                let a = v[v.len() - 2];
                let b = v[v.len() - 1];
                let c = a + b;
                if c > 1000 { v.push(1000); } else { v.push(c); }
            }
            v.truncate(n);
            v
        }
        5 => {
            // Max size, small values
            let n = 1000;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 5));
            }
            v
        }
        6 => {
            // Max size, max values
            let n = 1000;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 1000));
            }
            v
        }
        7 => {
            // Sorted ascending
            let n = rng.gen_range_usize(3, 100);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1000));
            }
            v.sort();
            v
        }
        8 => {
            // Sorted descending
            let n = rng.gen_range_usize(3, 100);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1000));
            }
            v.sort();
            v.reverse();
            v
        }
        9 => {
            // Many zeros mixed
            let n = rng.gen_range_usize(3, 200);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                if rng.next_u64() % 3 == 0 {
                    v.push(0);
                } else {
                    v.push(rng.gen_range_i32(1, 1000));
                }
            }
            v
        }
        _ => {
            // General random
            let n = rng.gen_range_usize(1, 500);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1000));
            }
            v
        }
    }
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
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let values = gen_mode(&mut rng, mode);
        if values.is_empty() || values.len() > 1000 {
            continue;
        }
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}