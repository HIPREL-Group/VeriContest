use vstd::prelude::*;

verus! {

pub fn generate_test_case(bits: i32) -> (result: i32)
    requires
        1 <= bits <= 1_000_000_000,
    ensures
        1 <= result <= 1_000_000_000,
{
    bits
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

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn print_json(n: i32) {
    println!("{{\"n\":{}}}", n);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);

    // Adversarial fixed inputs
    let fixed: Vec<i32> = vec![
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10,
        15, 16, 17, 31, 32, 33, 63, 64, 65,
        127, 128, 129, 255, 256, 257, 511, 512, 513,
        1023, 1024, 1025, 2047, 2048, 2049,
        (1 << 20) - 1, 1 << 20, (1 << 20) + 1,
        (1 << 29) - 1, 1 << 29, (1 << 29) + 1,
        (1 << 30) - 1, 1 << 30,
        1_000_000_000, 999_999_999, 999_999_937,
        123_456_789, 987_654_321,
    ];

    for &v in fixed.iter() {
        if v >= 1 && v <= 1_000_000_000 {
            let x = generate_test_case(v);
            print_json(x);
        }
    }

    // Adversarial modes
    // 0: small values
    // 1: powers of two
    // 2: powers of two minus 1
    // 3: powers of two plus 1
    // 4: alternating bit patterns (01010..)
    // 5: alternating bit patterns (10101..)
    // 6: all ones block
    // 7: large random
    // 8: medium random
    // 9: near max

    let total = 200usize;
    for t in 0..total {
        let mode = t % 10;
        let v: i32 = match mode {
            0 => rng.gen_range_i32(1, 100),
            1 => {
                let k = rng.gen_range_i32(0, 29);
                1i32 << k
            }
            2 => {
                let k = rng.gen_range_i32(1, 30);
                (1i32 << k) - 1
            }
            3 => {
                let k = rng.gen_range_i32(0, 29);
                (1i32 << k) + 1
            }
            4 => {
                // 0101...
                let k = rng.gen_range_i32(1, 15);
                let mut x = 0i32;
                for i in 0..k {
                    x |= 1 << (2 * i);
                }
                if x < 1 { 1 } else { x }
            }
            5 => {
                // 1010...
                let k = rng.gen_range_i32(1, 15);
                let mut x = 0i32;
                for i in 0..k {
                    x |= 1 << (2 * i + 1);
                }
                if x < 1 { 1 } else { x.min(1_000_000_000) }
            }
            6 => {
                let k = rng.gen_range_i32(2, 30);
                let x = (1i32 << k) - 1;
                x.min(1_000_000_000)
            }
            7 => rng.gen_range_i32(1, 1_000_000_000),
            8 => rng.gen_range_i32(1000, 1_000_000),
            _ => rng.gen_range_i32(900_000_000, 1_000_000_000),
        };
        let v = if v < 1 { 1 } else if v > 1_000_000_000 { 1_000_000_000 } else { v };
        let x = generate_test_case(v);
        print_json(x);
    }
}