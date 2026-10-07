use vstd::prelude::*;

verus! {

pub fn generate_test_case(bits: &Vec<u8>) -> (nums: Vec<i32>)
    requires
        1 <= bits.len() <= 100_000,
        forall|i: int| 0 <= i < bits.len() ==> (#[trigger] bits[i]) == 0u8 || bits[i] == 1u8,
    ensures
        1 <= nums.len() <= 100_000,
        nums.len() == bits.len(),
        forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] == 0i32 || nums[i] == 1i32,
{
    let n = bits.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == bits.len(),
            0 <= i <= n,
            nums.len() == i,
            forall|k: int| 0 <= k < bits.len() ==> (#[trigger] bits[k]) == 0u8 || bits[k] == 1u8,
            forall|k: int| 0 <= k < i as int ==> #[trigger] nums[k] == 0i32 || nums[k] == 1i32,
        decreases n - i,
    {
        let b = bits[i];
        if b == 0u8 {
            nums.push(0i32);
        } else {
            nums.push(1i32);
        }
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
    fn gen_bit(&mut self) -> u8 {
        (self.next_u64() & 1) as u8
    }
}

fn adversarial_case(rng: &mut Rng, mode: usize) -> Vec<u8> {
    match mode {
        0 => vec![1u8],
        1 => vec![0u8],
        2 => {
            let n = rng.gen_range_usize(1, 50);
            vec![1u8; n]
        }
        3 => {
            let n = rng.gen_range_usize(1, 50);
            vec![0u8; n]
        }
        4 => {
            let n = rng.gen_range_usize(2, 50);
            let mut v = vec![1u8; n];
            let z = rng.gen_range_usize(0, n - 1);
            v[z] = 0;
            v
        }
        5 => {
            let n = rng.gen_range_usize(3, 100);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push(if i % 2 == 0 { 1u8 } else { 0u8 });
            }
            v
        }
        6 => {
            let n = rng.gen_range_usize(10, 200);
            let mut v = Vec::with_capacity(n);
            let split = n / 2;
            for i in 0..n {
                v.push(if i < split { 1u8 } else { 0u8 });
            }
            v
        }
        7 => {
            let n = rng.gen_range_usize(10, 200);
            let mut v = vec![1u8; n];
            if n >= 3 {
                v[n / 3] = 0;
                v[2 * n / 3] = 0;
            }
            v
        }
        8 => {
            // Large
            let n = 100_000;
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push(if i % 7 == 0 { 0u8 } else { 1u8 });
            }
            v
        }
        9 => {
            // All ones large
            vec![1u8; 100_000]
        }
        10 => {
            // All zeros large
            vec![0u8; 100_000]
        }
        11 => {
            // One zero in middle
            let n = rng.gen_range_usize(5, 500);
            let mut v = vec![1u8; n];
            v[n / 2] = 0;
            v
        }
        _ => {
            let n = rng.gen_range_usize(1, 500);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_bit());
            }
            v
        }
    }
}

fn random_case(rng: &mut Rng) -> Vec<u8> {
    let n = rng.gen_range_usize(1, 1000);
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_bit());
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

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };
    let mut rng = Rng::new(seed);
    let total = 200usize;
    let adv_modes = 13usize;

    for t in 0..total {
        let bits = if t < adv_modes * 2 {
            adversarial_case(&mut rng, t % adv_modes)
        } else {
            random_case(&mut rng)
        };
        let nums = generate_test_case(&bits);
        print_json(&nums);
    }
}