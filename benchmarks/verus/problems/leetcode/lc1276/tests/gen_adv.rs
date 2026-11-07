use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    jumbo: i32,
    small: i32,
) -> (result: (i32, i32))
    ensures
        0 <= result.0 <= 10_000_000,
        0 <= result.1 <= 10_000_000,
{
    let jumbo = if jumbo < 0 { 0 } else if jumbo > 2500000 { 2500000 } else { jumbo };
    let max_small = 5000000 - 2 * jumbo;
    let small = if small < 0 { 0 } else if small > max_small { max_small } else { small };
    let tomato: i32 = 4 * jumbo + 2 * small;
    let cheese: i32 = jumbo + small;
    (tomato, cheese)
}

pub fn generate_invalid_odd_tomato(
    tomato_half: i32,
    cheese: i32,
) -> (result: (i32, i32))
    ensures
        0 <= result.0 <= 10_000_000,
        0 <= result.1 <= 10_000_000,
{
    let tomato_half = if tomato_half < 0 { 0 } else if tomato_half > 4999999 { 4999999 } else { tomato_half };
    let cheese = if cheese < 0 { 0 } else if cheese > 10000000 { 10000000 } else { cheese };
    let tomato: i32 = 2 * tomato_half + 1;
    (tomato, cheese)
}

pub fn generate_raw(
    tomato: i32,
    cheese: i32,
) -> (result: (i32, i32))
    ensures
        0 <= result.0 <= 10_000_000,
        0 <= result.1 <= 10_000_000,
{
    let tomato = if tomato < 0 { 0 } else if tomato > 10000000 { 10000000 } else { tomato };
    let cheese = if cheese < 0 { 0 } else if cheese > 10000000 { 10000000 } else { cheese };
    (tomato, cheese)
}

}

struct Rng { state: u64 }

impl Rng {
    fn new(seed: u64) -> Self { Self { state: seed.wrapping_add(0x9E3779B97F4A7C15) } }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn print_case(tomato: i32, cheese: i32) {
    let (tomato, cheese) = generate_raw(tomato, cheese);
    println!("{{\"tomato_slices\": {}, \"cheese_slices\": {}}}", tomato, cheese);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);

    // Adversarial fixed cases
    let fixed: Vec<(i32, i32)> = vec![
        (0, 0),
        (16, 7),
        (17, 4),
        (4, 17),
        (10_000_000, 2_500_000),
        (10_000_000, 5_000_000),
        (10_000_000, 3_000_000),
        (2, 1),
        (4, 1),
        (1, 0),
        (0, 1),
        (2, 0),
        (0, 10_000_000),
        (10_000_000, 0),
        (100, 50),
        (100, 25),
        (100, 26),
        (100, 49),
    ];
    for (t, c) in fixed.iter() {
        let (tt, cc) = generate_raw(*t, *c);
        print_case(tt, cc);
    }

    let total = 200;
    for t in 0..total {
        let mode = t % 10;
        match mode {
            0 => {
                // Fully valid: pick jumbo and small, compute tomato/cheese
                let j = rng.gen_range_i32(0, 2_500_000);
                let max_s = 5_000_000 - 2 * j;
                let max_s2 = if max_s > 5_000_000 { 5_000_000 } else { max_s };
                let s = rng.gen_range_i32(0, max_s2.max(0));
                let (tt, cc) = generate_test_case(j, s);
                print_case(tt, cc);
            }
            1 => {
                // small valid cases
                let j = rng.gen_range_i32(0, 100);
                let s = rng.gen_range_i32(0, 100);
                let (tt, cc) = generate_test_case(j, s);
                print_case(tt, cc);
            }
            2 => {
                // odd tomato - always invalid
                let th = rng.gen_range_i32(0, 4_999_999);
                let c = rng.gen_range_i32(0, 10_000_000);
                let (tt, cc) = generate_invalid_odd_tomato(th, c);
                print_case(tt, cc);
            }
            3 => {
                // tomato > 4*cheese
                let c = rng.gen_range_i32(0, 100);
                let tt = 4 * c + rng.gen_range_i32(2, 200);
                let tt = if tt > 10_000_000 { 10_000_000 } else { tt };
                let (a, b) = generate_raw(tt, c);
                print_case(a, b);
            }
            4 => {
                // tomato < 2*cheese
                let c = rng.gen_range_i32(100, 1000);
                let tt = 2 * c - rng.gen_range_i32(2, 100);
                let tt = if tt < 0 { 0 } else { tt };
                let (a, b) = generate_raw(tt, c);
                print_case(a, b);
            }
            5 => {
                // boundary: tomato = 2*cheese (all small)
                let c = rng.gen_range_i32(0, 5_000_000);
                let (a, b) = generate_test_case(0, c);
                print_case(a, b);
            }
            6 => {
                // boundary: tomato = 4*cheese (all jumbo)
                let c = rng.gen_range_i32(0, 2_500_000);
                let (a, b) = generate_test_case(c, 0);
                print_case(a, b);
            }
            7 => {
                // zero cases
                let t = rng.gen_range_i32(0, 10_000_000);
                let (a, b) = generate_raw(t, 0);
                print_case(a, b);
            }
            8 => {
                // zero tomato
                let c = rng.gen_range_i32(0, 10_000_000);
                let (a, b) = generate_raw(0, c);
                print_case(a, b);
            }
            _ => {
                // totally random
                let t = rng.gen_range_i32(0, 10_000_000);
                let c = rng.gen_range_i32(0, 10_000_000);
                let (a, b) = generate_raw(t, c);
                print_case(a, b);
            }
        }
    }
}
