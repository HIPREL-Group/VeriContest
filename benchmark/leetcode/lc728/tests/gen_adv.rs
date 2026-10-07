use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_left: i32, seed_right: i32, mutation_kind: u8) -> (result: (i32, i32))
    requires
        1 <= seed_left <= 10_000i32,
        1 <= seed_right <= 10_000i32,
    ensures
        1 <= result.0 <= result.1 <= 10_000,
{
    let lo = if seed_left <= seed_right { seed_left } else { seed_right };
    let hi = if seed_left <= seed_right { seed_right } else { seed_left };

    if mutation_kind == 0 {
        (lo, hi)
    } else if mutation_kind == 1 {
        (lo, lo)
    } else if mutation_kind == 2 {
        (1, 10_000)
    } else if mutation_kind == 3 {
        (1, hi)
    } else if mutation_kind == 4 {
        (lo, 10_000)
    } else if mutation_kind == 5 && lo < 10_000 {
        (lo + 1, if lo + 1 > hi { lo + 1 } else { hi })
    } else if mutation_kind == 6 && hi > 1 {
        (if lo < hi { lo } else { hi - 1 }, hi - 1)
    } else if mutation_kind == 7 {
        (hi, hi)
    } else if mutation_kind == 8 {
        (1, 1)
    } else if mutation_kind == 9 {
        (10_000, 10_000)
    } else if mutation_kind == 10 {
        let mid = lo + (hi - lo) / 2;
        (mid, mid)
    } else {
        (lo, hi)
    }
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
        lo + (self.next_u64() % span) as i32
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
    let seed_values: Vec<i32> = vec![
        1, 2, 9, 10, 11, 22, 48, 55, 66, 77, 100, 128, 999, 1000, 1111, 5000, 9999, 10_000,
    ];

    let total = 200usize;
    for t in 0..total {
        let (sl, sr, mk) = if t < 30 {
            let i = t as usize;
            let sl = seed_values[i % seed_values.len()];
            let sr = seed_values[(i / 3) % seed_values.len()];
            let mk = (t % 11) as u8;
            (sl, sr, mk)
        } else {
            let sl = rng.gen_range_i32(1, 10_000);
            let sr = rng.gen_range_i32(1, 10_000);
            let mk = (rng.next_u64() % 11) as u8;
            (sl, sr, mk)
        };
        let (left, right) = generate_test_case(sl, sr, mk);
        println!("{{\"left\": {}, \"right\": {}}}", left, right);
    }
}
