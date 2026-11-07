use vstd::prelude::*;

verus! {

pub fn generate_test_case(low_val: i32, high_val: i32) -> (result: (i32, i32))
    requires
        10 <= low_val <= high_val <= 1000000000,
    ensures
        10 <= result.0 <= result.1 <= 1000000000,
{
    (low_val, high_val)
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

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn emit(low: i32, high: i32) {
    let (l, h) = generate_test_case(low, high);
    println!("{{\"low\": {}, \"high\": {}}}", l, h);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };
    let mut rng = Rng::new(seed);

    // Adversarial boundary cases
    let boundaries: Vec<(i32, i32)> = vec![
        (10, 10),
        (10, 11),
        (10, 12),
        (10, 13),
        (10, 99),
        (10, 100),
        (10, 1000000000),
        (12, 12),
        (12, 13),
        (23, 23),
        (100, 300),
        (1000, 13000),
        (123, 123),
        (123, 234),
        (100, 123),
        (124, 234),
        (89, 89),
        (999999999, 1000000000),
        (1000000000, 1000000000),
        (12345678, 123456789),
        (123456789, 123456789),
        (123456789, 1000000000),
        (100000000, 1000000000),
        (99, 100),
        (1234, 1234),
        (1234, 2345),
        (98, 100),
        (789, 789),
        (6789, 6789),
        (56789, 56789),
        (456789, 456789),
        (3456789, 3456789),
        (23456789, 23456789),
        (10, 20),
        (20, 30),
        (90, 100),
        (100, 200),
        (200, 300),
        (13, 23),
        (24, 34),
        (35, 45),
        (46, 56),
        (57, 67),
        (68, 78),
        (79, 89),
    ];

    let mut count = 0;
    for &(l, h) in &boundaries {
        if 10 <= l && l <= h && h <= 1000000000 {
            emit(l, h);
            count += 1;
        }
    }

    // Mode-based random generation
    while count < 220 {
        let mode = (rng.next_u64() % 10) as u32;
        let (l, h): (i32, i32) = match mode {
            0 => {
                // small range near low boundary
                let l = rng.gen_range_i32(10, 100);
                let span = rng.gen_range_i32(0, 50);
                let h = if (l as i64 + span as i64) > 1000000000 { 1000000000 } else { l + span };
                (l, h)
            }
            1 => {
                // near high boundary
                let h = 1000000000i32;
                let l = rng.gen_range_i32(999000000, 1000000000);
                (l, h)
            }
            2 => {
                // wide range
                (10, 1000000000)
            }
            3 => {
                // tight range
                let l = rng.gen_range_i32(10, 1000000000);
                (l, l)
            }
            4 => {
                // medium range
                let l = rng.gen_range_i32(10, 1000);
                let h = rng.gen_range_i32(l, 100000);
                (l, h)
            }
            5 => {
                // around known sequential digits
                let seqs: [i32; 10] = [12, 123, 1234, 12345, 123456, 1234567, 12345678, 123456789, 234, 2345];
                let idx = (rng.next_u64() % 10) as usize;
                let s = seqs[idx];
                let delta1 = rng.gen_range_i32(0, 100);
                let delta2 = rng.gen_range_i32(0, 100);
                let l_raw = s as i64 - delta1 as i64;
                let h_raw = s as i64 + delta2 as i64;
                let l = if l_raw < 10 { 10 } else { l_raw as i32 };
                let h = if h_raw > 1000000000 { 1000000000 } else { h_raw as i32 };
                let h = if h < l { l } else { h };
                (l, h)
            }
            6 => {
                // two-digit only
                let l = rng.gen_range_i32(10, 98);
                let h = rng.gen_range_i32(l, 99);
                (l, h)
            }
            7 => {
                // three-digit
                let l = rng.gen_range_i32(100, 998);
                let h = rng.gen_range_i32(l, 999);
                (l, h)
            }
            8 => {
                // completely random
                let a = rng.gen_range_i32(10, 1000000000);
                let b = rng.gen_range_i32(10, 1000000000);
                if a <= b { (a, b) } else { (b, a) }
            }
            _ => {
                // single-value at sequential
                let seqs: [i32; 9] = [12, 23, 34, 45, 56, 67, 78, 89, 123];
                let idx = (rng.next_u64() % 9) as usize;
                let s = seqs[idx];
                (s, s)
            }
        };

        if 10 <= l && l <= h && h <= 1000000000 {
            emit(l, h);
            count += 1;
        }
    }
}