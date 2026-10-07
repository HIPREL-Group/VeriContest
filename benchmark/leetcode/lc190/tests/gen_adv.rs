use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (res: i32)
    requires
        0 <= n <= 2_147_483_646,
        n % 2 == 0,
    ensures
        0 <= res <= 2_147_483_646,
        res % 2 == 0,
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

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn to_even(n: i32) -> i32 {
    let mut x = n;
    if x < 0 {
        x = 0;
    }
    if x > 2_147_483_646 {
        x = 2_147_483_646;
    }
    if x % 2 != 0 {
        if x == 2_147_483_646 {
            x -= 1;
            // wait, 2_147_483_646 is even actually
        } else {
            x += 1;
        }
    }
    // Ensure final bounds
    if x < 0 {
        x = 0;
    }
    if x > 2_147_483_646 {
        x = 2_147_483_646;
    }
    if x % 2 != 0 {
        x -= 1;
        if x < 0 {
            x = 0;
        }
    }
    x
}

fn pick_for_mode(rng: &mut Rng, mode: usize) -> i32 {
    match mode {
        0 => 0,
        1 => 2,
        2 => 2_147_483_646,
        3 => 2_147_483_644,
        4 => {
            // Random small even number
            let v = rng.gen_range_i32(0, 1000);
            to_even(v)
        }
        5 => {
            // Large powers of two
            let bits = (rng.next_u64() % 31) as u32;
            let v = 1i64 << bits;
            let vv = if v > 2_147_483_646 { 2_147_483_646 } else { v as i32 };
            to_even(vv)
        }
        6 => {
            // Single bit set in high positions
            let bits = 1 + (rng.next_u64() % 30) as u32;
            let v = 1i64 << bits;
            let vv = if v > 2_147_483_646 { 2_147_483_646 } else { v as i32 };
            to_even(vv)
        }
        7 => {
            // Palindromic-ish patterns
            let v = 0x12345678i32 & 0x7FFFFFFE;
            to_even(v)
        }
        8 => {
            // All low bits set
            let bits = 1 + (rng.next_u64() % 30) as u32;
            let v = ((1i64 << bits) - 1) as i32;
            to_even(v & 0x7FFFFFFE)
        }
        9 => {
            // Alternating bits
            let v = 0x2AAAAAAAi32;
            to_even(v)
        }
        _ => {
            // Fully random in range
            let v = rng.gen_range_i32(0, 2_147_483_646);
            to_even(v)
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
        let n = pick_for_mode(&mut rng, mode);
        let out = generate_test_case(n);
        println!("{{\"n\": {}}}", out);
    }
}