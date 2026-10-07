use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    k_val: i32,
    values: &Vec<i32>,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= n <= 100000,
        values.len() == n,
        0 <= k_val < n as i32,
        forall |i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] < 1_073_741_824,
    ensures
        1 <= result.0.len() <= 100000,
        0 <= result.1 < result.0.len() as i32,
        forall |i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] < 1_073_741_824,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            nums.len() == i,
            i <= n,
            values.len() == n,
            forall |j: int| 0 <= j < i as int ==> 0 <= #[trigger] nums[j] < 1_073_741_824,
            forall |j: int| 0 <= j < i as int ==> nums[j] == values[j],
            forall |j: int| 0 <= j < values.len() ==> 0 <= #[trigger] values[j] < 1_073_741_824,
        decreases n - i,
    {
        let v = values[i];
        assert(0 <= v < 1_073_741_824);
        nums.push(v);
        i = i + 1;
    }

    (nums, k_val)
}

} // verus!

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

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

const MAXV: i32 = 1_073_741_823; // 2^30 - 1

fn gen_values(rng: &mut Rng, n: usize, mode: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    match mode {
        0 => {
            // all zeros
            for _ in 0..n {
                v.push(0);
            }
        }
        1 => {
            // all max
            for _ in 0..n {
                v.push(MAXV);
            }
        }
        2 => {
            // single high bit
            for _ in 0..n {
                v.push(1 << 29);
            }
        }
        3 => {
            // random small
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 15));
            }
        }
        4 => {
            // alternating pattern
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(0xAAAAAAA);
                } else {
                    v.push(0x5555555);
                }
            }
        }
        5 => {
            // powers of two
            for i in 0..n {
                v.push(1 << ((i as i32) % 30));
            }
        }
        6 => {
            // one zero in middle
            for i in 0..n {
                if i == n / 2 {
                    v.push(0);
                } else {
                    v.push(rng.gen_range_i32(0, MAXV));
                }
            }
        }
        7 => {
            // ascending
            for i in 0..n {
                v.push((i as i32) % MAXV);
            }
        }
        8 => {
            // all same random
            let x = rng.gen_range_i32(0, MAXV);
            for _ in 0..n {
                v.push(x);
            }
        }
        9 => {
            // sparse bits
            for _ in 0..n {
                let b1 = rng.gen_range_i32(0, 29);
                let b2 = rng.gen_range_i32(0, 29);
                v.push((1 << b1) | (1 << b2));
            }
        }
        _ => {
            // fully random
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, MAXV));
            }
        }
    }
    v
}

fn print_json(nums: &[i32], k: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", nums[i]);
    }
    println!("],\"k\":{}}}", k);
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
        let n: usize = match t % 7 {
            0 => 1,
            1 => 2,
            2 => rng.gen_range_usize(3, 10),
            3 => rng.gen_range_usize(10, 100),
            4 => rng.gen_range_usize(100, 1000),
            5 => rng.gen_range_usize(1000, 10000),
            _ => {
                if mode == 1 || mode == 8 {
                    100000
                } else {
                    rng.gen_range_usize(50, 500)
                }
            }
        };

        let values = gen_values(&mut rng, n, mode);
        let k = if n == 1 { 0 } else { rng.gen_range_usize(0, n - 1) as i32 };

        let (nums, k_out) = generate_test_case(n, k, &values);
        print_json(&nums, k_out);
    }
}