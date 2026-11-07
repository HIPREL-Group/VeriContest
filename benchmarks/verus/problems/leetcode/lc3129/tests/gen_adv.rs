use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_zero: i32,
    seed_one: i32,
    seed_limit: i32,
    mutation_kind: u8,
) -> (result: (i32, i32, i32))
    requires
        1 <= seed_zero <= 200,
        1 <= seed_one <= 200,
        1 <= seed_limit <= 200,
    ensures
        1 <= result.0 <= 200,
        1 <= result.1 <= 200,
        1 <= result.2 <= 200,
{
    if mutation_kind == 0 {
        (seed_zero, seed_one, seed_limit)
    } else if mutation_kind == 1 && seed_zero < 200 {
        (seed_zero + 1, seed_one, seed_limit)
    } else if mutation_kind == 2 && seed_zero > 1 {
        (seed_zero - 1, seed_one, seed_limit)
    } else if mutation_kind == 3 && seed_one < 200 {
        (seed_zero, seed_one + 1, seed_limit)
    } else if mutation_kind == 4 && seed_one > 1 {
        (seed_zero, seed_one - 1, seed_limit)
    } else if mutation_kind == 5 && seed_limit < 200 {
        (seed_zero, seed_one, seed_limit + 1)
    } else if mutation_kind == 6 && seed_limit > 1 {
        (seed_zero, seed_one, seed_limit - 1)
    } else if mutation_kind == 7 {
        (1, seed_one, seed_limit)
    } else if mutation_kind == 8 {
        (200, seed_one, seed_limit)
    } else if mutation_kind == 9 {
        (seed_zero, 1, seed_limit)
    } else if mutation_kind == 10 {
        (seed_zero, 200, seed_limit)
    } else if mutation_kind == 11 {
        (seed_zero, seed_one, 1)
    } else if mutation_kind == 12 {
        (seed_zero, seed_one, 200)
    } else if mutation_kind == 13 {
        (1, 1, 1)
    } else if mutation_kind == 14 {
        (200, 200, 200)
    } else if mutation_kind == 15 {
        let hz = seed_zero / 2;
        if hz >= 1 { (hz, seed_one, seed_limit) } else { (1, seed_one, seed_limit) }
    } else if mutation_kind == 16 {
        let ho = seed_one / 2;
        if ho >= 1 { (seed_zero, ho, seed_limit) } else { (seed_zero, 1, seed_limit) }
    } else if mutation_kind == 17 {
        let hl = seed_limit / 2;
        if hl >= 1 { (seed_zero, seed_one, hl) } else { (seed_zero, seed_one, 1) }
    } else if mutation_kind == 18 {
        let dz = if seed_zero <= 100 { seed_zero * 2 } else { 200 };
        (dz, seed_one, seed_limit)
    } else if mutation_kind == 19 {
        let d_one = if seed_one <= 100 { seed_one * 2 } else { 200 };
        (seed_zero, d_one, seed_limit)
    } else if mutation_kind == 20 {
        let dl = if seed_limit <= 100 { seed_limit * 2 } else { 200 };
        (seed_zero, seed_one, dl)
    } else if mutation_kind == 21 {
        (seed_one, seed_zero, seed_limit)
    } else if mutation_kind == 22 {
        (seed_zero, seed_one, seed_zero)
    } else if mutation_kind == 23 {
        (seed_zero, seed_one, seed_one)
    } else {
        (seed_zero, seed_one, seed_limit)
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
        lo + ((self.next_u64() % span) as i32)
    }
}

// Match gen.rs: keep inputs tiny so reference oracle (recursive code.rs) finishes.
const MAX_SEED: i32 = 12;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let modes = 24usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let sz = rng.gen_range_i32(1, MAX_SEED);
        let so = rng.gen_range_i32(1, MAX_SEED);
        let sl = rng.gen_range_i32(1, MAX_SEED);
        let mk = mode as u8;
        let (mut zero, mut one, mut limit) = generate_test_case(sz, so, sl, mk);
        // Clamp like gen.rs so reference_oracle stays fast (recursive code.rs).
        if zero > MAX_SEED {
            zero = MAX_SEED;
        }
        if one > MAX_SEED {
            one = MAX_SEED;
        }
        if limit > MAX_SEED {
            limit = MAX_SEED;
        }
        println!(
            "{{\"zero\":{},\"one\":{},\"limit\":{}}}",
            zero, one, limit
        );
    }
}
