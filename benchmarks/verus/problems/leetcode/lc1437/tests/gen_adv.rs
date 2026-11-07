use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    k: i32,
    bits: &Vec<u8>,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= n <= 100000,
        0 <= k <= n as i32,
        bits.len() == n,
        forall |i: int| 0 <= i < bits.len() ==> #[trigger] bits[i] <= 1,
    ensures
        1 <= result.0.len() <= 100000,
        0 <= result.1 <= result.0.len() as i32,
        result.1 == k,
        forall |i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 1,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == bits.len(),
            nums.len() == i,
            forall |j: int| 0 <= j < i as int ==> 0 <= #[trigger] nums[j] <= 1,
            forall |j: int| 0 <= j < bits.len() ==> #[trigger] bits[j] <= 1,
        decreases n - i,
    {
        let b = bits[i];
        let v: i32 = if b == 0 { 0 } else { 1 };
        assert(b <= 1);
        assert(0 <= v && v <= 1);
        nums.push(v);
        i = i + 1;
    }
    assert(nums.len() == n);
    (nums, k)
}

}

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(1) }
    }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
}

fn build_bits_mode(rng: &mut Rng, mode: usize, n: usize) -> (Vec<u8>, i32) {
    let mut bits: Vec<u8> = vec![0u8; n];
    let k: i32;
    match mode {
        0 => {
            // all zeros
            k = rng.gen_usize(0, n) as i32;
        }
        1 => {
            // all ones
            for i in 0..n { bits[i] = 1; }
            k = rng.gen_usize(0, n) as i32;
        }
        2 => {
            // single one
            let idx = rng.gen_usize(0, n - 1);
            bits[idx] = 1;
            k = rng.gen_usize(0, n) as i32;
        }
        3 => {
            // two adjacent ones
            if n >= 2 {
                let idx = rng.gen_usize(0, n - 2);
                bits[idx] = 1;
                bits[idx + 1] = 1;
            } else {
                bits[0] = 1;
            }
            k = rng.gen_usize(0, n) as i32;
        }
        4 => {
            // evenly spaced with gap g
            let g = rng.gen_usize(1, std::cmp::max(1, n));
            let mut i = 0;
            while i < n {
                bits[i] = 1;
                i += g;
            }
            k = rng.gen_usize(0, n) as i32;
        }
        5 => {
            // k = 0, random bits
            for i in 0..n {
                bits[i] = (rng.next_u64() & 1) as u8;
            }
            k = 0;
        }
        6 => {
            // k = n
            for i in 0..n {
                bits[i] = (rng.next_u64() & 1) as u8;
            }
            k = n as i32;
        }
        7 => {
            // random bits
            for i in 0..n {
                bits[i] = (rng.next_u64() & 1) as u8;
            }
            k = rng.gen_usize(0, n) as i32;
        }
        8 => {
            // ones only at endpoints
            bits[0] = 1;
            bits[n - 1] = 1;
            k = rng.gen_usize(0, n) as i32;
        }
        9 => {
            // boundary-case: spacing exactly k
            let kk = rng.gen_usize(1, std::cmp::max(1, n));
            let mut i = 0;
            while i < n {
                bits[i] = 1;
                i += kk;
            }
            k = kk as i32;
        }
        _ => {
            // sparse random
            let m = rng.gen_usize(0, n);
            for _ in 0..m {
                let idx = rng.gen_usize(0, n - 1);
                bits[idx] = 1;
            }
            k = rng.gen_usize(0, n) as i32;
        }
    }
    (bits, k)
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
    let seed: u64 = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };
    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n: usize = match mode {
            0 => 1 + (t % 5),
            1 => 10,
            2 => 1 + (t % 20),
            3 => 2 + (t % 10),
            4 => 50 + (t % 50),
            5 => 100,
            6 => 100,
            7 => 500 + (t % 500),
            8 => 2 + (t % 100),
            9 => 20 + (t % 30),
            _ => {
                let r = rng.gen_usize(1, 10000);
                r
            }
        };
        let n = if n < 1 { 1 } else if n > 100000 { 100000 } else { n };
        let (bits, k) = build_bits_mode(&mut rng, mode, n);
        let k = if k < 0 { 0 } else if k > n as i32 { n as i32 } else { k };
        let (nums, k) = generate_test_case(n, k, &bits);
        print_json(&nums, k);
    }
}