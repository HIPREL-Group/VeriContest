use vstd::prelude::*;

verus! {

pub fn generate_test_case(x: i32) -> (res: i32)
    requires
        i32::MIN <= x <= i32::MAX,
    ensures
        i32::MIN <= res <= i32::MAX,
{
    x
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

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        let span = (hi as i128 - lo as i128 + 1) as u128;
        let v = (self.next_u64() as u128) % span;
        lo + v as i64
    }
}

fn reverse_i64(mut n: i64) -> i64 {
    let mut r: i64 = 0;
    while n > 0 {
        r = r * 10 + (n % 10);
        n /= 10;
    }
    r
}

fn make_palindrome_up_to(rng: &mut Rng, max_digits: u32) -> i32 {
    // pick random digit count
    let d = (rng.gen_range_i64(1, max_digits as i64)) as u32;
    let mut digits: Vec<i64> = Vec::new();
    let half = (d + 1) / 2;
    for i in 0..half {
        let lo = if i == 0 { 1 } else { 0 };
        digits.push(rng.gen_range_i64(lo, 9));
    }
    // mirror
    let mut full: Vec<i64> = Vec::new();
    for i in 0..half {
        full.push(digits[i as usize]);
    }
    let start = if d % 2 == 1 { (half as i64) - 2 } else { (half as i64) - 1 };
    let mut k = start;
    while k >= 0 {
        full.push(digits[k as usize]);
        k -= 1;
    }
    let mut val: i64 = 0;
    for &dig in &full {
        val = val * 10 + dig;
    }
    if val > i32::MAX as i64 {
        val = val % (i32::MAX as i64 + 1);
    }
    val as i32
}

fn pick_for_mode(rng: &mut Rng, mode: usize) -> i32 {
    match mode {
        0 => 0,
        1 => {
            // small palindrome
            let v = rng.gen_range_i64(0, 9);
            v as i32
        }
        2 => {
            // small non-palindrome negative
            let v = rng.gen_range_i64(-1000, -1);
            v as i32
        }
        3 => {
            // random palindrome
            make_palindrome_up_to(rng, 9)
        }
        4 => {
            // multiple of 10 (not palindrome except 0)
            let v = rng.gen_range_i64(1, 200_000_000);
            (v * 10) as i32
        }
        5 => {
            // random positive
            rng.gen_range_i64(0, i32::MAX as i64) as i32
        }
        6 => {
            // random negative
            rng.gen_range_i64(i32::MIN as i64, -1) as i32
        }
        7 => {
            // boundary values
            let choices = [i32::MIN, i32::MAX, -2147483647, 2147483646, -1, 1];
            choices[(rng.next_u64() as usize) % choices.len()]
        }
        8 => {
            // near-palindrome: palindrome +/- 1
            let p = make_palindrome_up_to(rng, 8) as i64;
            let delta = rng.gen_range_i64(-1, 1);
            (p + delta) as i32
        }
        9 => {
            // numbers that read as palindrome when reversed (odd/even length edge)
            let v = rng.gen_range_i64(10, 99);
            // e.g., 11, 22 palindromes. Just use v.
            let r = reverse_i64(v);
            if r == v { v as i32 } else { (v * 100 + v) as i32 }
        }
        _ => {
            // random full range
            rng.gen_range_i64(i32::MIN as i64, i32::MAX as i64) as i32
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
        let x = pick_for_mode(&mut rng, mode);
        let v = generate_test_case(x);
        println!("{{\"x\":{}}}", v);
    }
}