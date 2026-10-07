use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (res: i32)
    requires
        -2_147_483_648 <= n <= 2_147_483_647,
    ensures
        -2_147_483_648 <= res <= 2_147_483_647,
        res == n,
{
    n
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
        self.state = self
            .state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let span = (hi as i128 - lo as i128 + 1) as u128;
        let v = (self.next_u64() as u128) % span;
        lo + v as i64
    }
}

fn clamp_i32(v: i64) -> i32 {
    if v < i32::MIN as i64 {
        i32::MIN
    } else if v > i32::MAX as i64 {
        i32::MAX
    } else {
        v as i32
    }
}

fn print_n(n: i32) {
    println!("{{\"n\":{}}}", n);
}

fn powers_of_three() -> Vec<i64> {
    let mut v = Vec::new();
    let mut p: i64 = 1;
    while p <= i32::MAX as i64 {
        v.push(p);
        p *= 3;
    }
    v
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);

    // Adversarial fixed cases
    let mut fixed: Vec<i32> = Vec::new();
    fixed.push(0);
    fixed.push(1);
    fixed.push(-1);
    fixed.push(2);
    fixed.push(3);
    fixed.push(-3);
    fixed.push(9);
    fixed.push(27);
    fixed.push(-27);
    fixed.push(45);
    fixed.push(i32::MAX);
    fixed.push(i32::MIN);
    fixed.push(i32::MIN + 1);
    fixed.push(i32::MAX - 1);

    let p3 = powers_of_three();
    for &p in &p3 {
        fixed.push(p as i32);
        fixed.push(-(p as i32));
        if p + 1 <= i32::MAX as i64 {
            fixed.push((p + 1) as i32);
        }
        if p - 1 >= 1 {
            fixed.push((p - 1) as i32);
        }
    }

    // powers of 2 (common bug: mixing up)
    let mut p2: i64 = 1;
    while p2 <= i32::MAX as i64 {
        fixed.push(p2 as i32);
        p2 *= 2;
    }

    // 6^k, 9^k (multiples that might fool naive)
    let mut pk: i64 = 1;
    while pk <= i32::MAX as i64 {
        fixed.push(pk as i32);
        pk *= 6;
    }

    for n in fixed {
        let r = generate_test_case(n);
        print_n(r);
    }

    // Mode-based generation
    let total = 200usize;
    for t in 0..total {
        let mode = t % 10;
        let n: i32 = match mode {
            0 => {
                // small random near 0
                let v = rng.gen_range_i64(-100, 100);
                v as i32
            }
            1 => {
                // random positive
                let v = rng.gen_range_i64(1, 2_147_483_647);
                v as i32
            }
            2 => {
                // random negative
                let v = rng.gen_range_i64(-2_147_483_648, -1);
                v as i32
            }
            3 => {
                // exact power of three
                let idx = (rng.next_u64() as usize) % p3.len();
                p3[idx] as i32
            }
            4 => {
                // negative power of three
                let idx = (rng.next_u64() as usize) % p3.len();
                -(p3[idx] as i32)
            }
            5 => {
                // power of three +/- 1
                let idx = (rng.next_u64() as usize) % p3.len();
                let delta = rng.gen_range_i64(-2, 2);
                clamp_i32(p3[idx] + delta)
            }
            6 => {
                // multiple of 3 but not power
                let k = rng.gen_range_i64(2, 1_000_000);
                let v = k * 3;
                clamp_i32(v)
            }
            7 => {
                // power of 2
                let shift = (rng.next_u64() as u32) % 31;
                1i32 << shift
            }
            8 => {
                // extremes
                match (rng.next_u64() % 4) as u8 {
                    0 => i32::MAX,
                    1 => i32::MIN,
                    2 => 0,
                    _ => 1,
                }
            }
            _ => {
                // full random
                let v = rng.gen_range_i64(-2_147_483_648, 2_147_483_647);
                v as i32
            }
        };

        let r = generate_test_case(n);
        print_n(r);
    }
}