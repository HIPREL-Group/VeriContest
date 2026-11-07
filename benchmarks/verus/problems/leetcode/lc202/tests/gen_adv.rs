use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1i32 <= seed <= i32::MAX,
    ensures
        1 <= result <= i32::MAX,
{
    if mutation_kind == 0 {
        seed                                          // identity
    } else if mutation_kind == 1 && seed < i32::MAX {
        seed + 1                                      // nudge up
    } else if mutation_kind == 2 && seed > 1 {
        seed - 1                                      // nudge down
    } else if mutation_kind == 3 {
        if seed >= -1_073_741_823 && seed <= 1_073_741_823 {
            if seed * 2 >= 1 { seed * 2 } else { seed } // double
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        if seed / 2 >= 1 { seed / 2 } else { seed }  // halve
    } else if mutation_kind == 5 {
        1                                             // min boundary
    } else if mutation_kind == 6 {
        i32::MAX                                      // max boundary
    } else if mutation_kind == 7 {
        if seed >= 1 { seed } else { 1 }              // absolute value (clamped)
    } else if mutation_kind == 8 {
        // square root region: small values
        if seed <= 46340 { seed } else { 46340 }
    } else if mutation_kind == 9 {
        // force a known happy number seed region
        if seed <= 100 { seed } else { 100 }
    } else {
        seed                                          // fallback
    }
}

} // verus!
struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }
    fn gen_u8(&mut self) -> u8 {
        (self.next_u64() % 256) as u8
    }
}

fn print_n(n: i32) {
    println!("{{\"n\":{}}}", n);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let mut rng = Rng::new(seed);

    let seeds: Vec<i32> = vec![
        19, 2,
        1, 7, 10, 13, 23, 28, 44, 49, 68, 79, 82, 86, 91, 94, 97, 100,
        3, 4, 5, 6, 8, 9, 11, 12, 14, 15, 16, 17, 18, 20,
        i32::MAX, i32::MAX - 1, i32::MAX / 2,
        10, 100, 1000, 10000, 100000, 1000000, 10000000, 100000000, 1000000000,
        1, 2, 3, 4, 5, 50, 99, 101, 999, 1001,
        999999999, 888888888, 777777777,
    ];

    for &s in &seeds {
        for mk in 0..=10u8 {
            let n = generate_test_case(s, mk);
            print_n(n);
        }
    }

    for _ in 0..200 {
        let s = rng.gen_range_i64(1, i32::MAX as i64) as i32;
        let mk = rng.gen_u8() % 11;
        let n = generate_test_case(s, mk);
        print_n(n);
    }
}
