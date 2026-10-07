use vstd::prelude::*;

verus! {

pub fn generate_test_case(num: i32) -> (result: i32)
    requires
        1000 <= num <= 9999,
    ensures
        1000 <= result <= 9999,
{
    num
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

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn digits_to_num(a: i32, b: i32, c: i32, d: i32) -> i32 {
    a * 1000 + b * 100 + c * 10 + d
}

fn pick_for_mode(rng: &mut Rng, mode: usize) -> i32 {
    match mode {
        0 => 1000,
        1 => 9999,
        2 => {
            // all same digits
            let d = rng.gen_range_i32(1, 9);
            digits_to_num(d, d, d, d)
        }
        3 => {
            // many zeros
            let d = rng.gen_range_i32(1, 9);
            digits_to_num(d, 0, 0, 0)
        }
        4 => {
            // one non-zero leading, others zero/small
            let d = rng.gen_range_i32(1, 9);
            let e = rng.gen_range_i32(0, 9);
            digits_to_num(d, 0, 0, e)
        }
        5 => {
            // ascending
            let a = rng.gen_range_i32(1, 6);
            digits_to_num(a, a+1, a+2, a+3)
        }
        6 => {
            // descending
            let a = rng.gen_range_i32(4, 9);
            digits_to_num(a, a-1, a-2, a-3)
        }
        7 => {
            // two pairs
            let a = rng.gen_range_i32(1, 9);
            let b = rng.gen_range_i32(0, 9);
            digits_to_num(a, b, a, b)
        }
        8 => {
            // contains 0
            let a = rng.gen_range_i32(1, 9);
            let b = rng.gen_range_i32(0, 9);
            let c = rng.gen_range_i32(0, 9);
            digits_to_num(a, 0, b, c)
        }
        9 => {
            // small values
            rng.gen_range_i32(1000, 1100)
        }
        _ => {
            // fully random
            rng.gen_range_i32(1000, 9999)
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
        let mut num = pick_for_mode(&mut rng, mode);
        if num < 1000 {
            num = 1000;
        }
        if num > 9999 {
            num = 9999;
        }
        let result = generate_test_case(num);
        println!("{{\"num\": {}}}", result);
    }
}