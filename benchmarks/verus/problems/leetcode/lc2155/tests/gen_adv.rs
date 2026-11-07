use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    bits: &Vec<u8>,
) -> (nums: Vec<i32>)
    requires
        1 <= bits.len() <= 100000,
        forall|i: int| 0 <= i < bits.len() ==> (#[trigger] bits[i]) == 0u8 || bits[i] == 1u8,
    ensures
        1 <= nums.len() <= 100000,
        forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] == 0 || nums[i] == 1,
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
            forall|k: int| 0 <= k < i as int ==> (#[trigger] nums[k] == 0 || nums[k] == 1),
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

struct Rng { state: u64 }

impl Rng {
    fn new(seed: u64) -> Self { Self { state: seed.wrapping_add(0x9E3779B97F4A7C15) } }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn range(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize) % span
    }
    fn bit(&mut self) -> u8 { (self.next_u64() & 1) as u8 }
}

fn build(n: usize, f: impl Fn(usize) -> u8) -> Vec<u8> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n { v.push(f(i)); }
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

fn make_bits(rng: &mut Rng, mode: usize, n: usize) -> Vec<u8> {
    match mode {
        0 => build(n, |_| 0),
        1 => build(n, |_| 1),
        2 => build(n, |i| (i % 2) as u8),
        3 => build(n, |i| ((i + 1) % 2) as u8),
        4 => build(n, |i| if i < n/2 { 0 } else { 1 }),
        5 => build(n, |i| if i < n/2 { 1 } else { 0 }),
        6 => {
            let mut v = build(n, |_| 0);
            if n > 0 { v[0] = 1; }
            v
        }
        7 => {
            let mut v = build(n, |_| 0);
            if n > 0 { v[n-1] = 1; }
            v
        }
        8 => {
            let mut v = Vec::with_capacity(n);
            for _ in 0..n { v.push(rng.bit()); }
            v
        }
        9 => {
            // mostly zeros, few ones
            let mut v = build(n, |_| 0);
            let ones = (n / 20).max(1);
            for _ in 0..ones {
                let idx = rng.range(0, n-1);
                v[idx] = 1;
            }
            v
        }
        _ => {
            // mostly ones, few zeros
            let mut v = build(n, |_| 1);
            let zeros = (n / 20).max(1);
            for _ in 0..zeros {
                let idx = rng.range(0, n-1);
                v[idx] = 0;
            }
            v
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => 1 + (t % 5),
            1 => 100_000,
            2 => 2 + (t % 10),
            3 => 99_999,
            4 => 2 + (t % 16),
            5 => 1000,
            6 => if t % 2 == 0 { 1 } else { 50_000 },
            7 => 256,
            8 => rng.range(1, 2000),
            9 => 10_000,
            _ => rng.range(1, 100_000),
        };
        let bits = make_bits(&mut rng, mode, n);
        let nums = generate_test_case(&bits);
        print_json(&nums);
    }
}