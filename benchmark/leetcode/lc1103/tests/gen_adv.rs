use vstd::prelude::*;

verus! {

pub struct Input {
    pub candies: i32,
    pub num_people: i32,
}

pub fn generate_test_case(
    base_candies: i32,
    extra_candies: i32,
    base_people: i32,
    extra_people: i32,
) -> (input: Input)
    requires
        1 <= base_candies <= 1_000_000_000,
        0 <= extra_candies,
        base_candies as int + extra_candies as int <= 1_000_000_000,
        1 <= base_people <= 1000,
        0 <= extra_people,
        base_people as int + extra_people as int <= 1000,
    ensures
        1 <= input.candies <= 1_000_000_000,
        1 <= input.num_people <= 1000,
{
    let candies = base_candies + extra_candies;
    let num_people = base_people + extra_people;

    assert(1 <= candies);
    assert(candies <= 1_000_000_000);
    assert(1 <= num_people);
    assert(num_people <= 1000);

    Input { candies, num_people }
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

    fn gen_range_u32(&mut self, lo: u32, hi: u32) -> u32 {
        assert!(lo <= hi);
        let span = (hi as u64) - (lo as u64) + 1;
        lo + (self.next_u64() % span) as u32
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_case(base_candies: i32, extra_candies: i32, base_people: i32, extra_people: i32) -> Input {
    generate_test_case(base_candies, extra_candies, base_people, extra_people)
}

fn adversarial_case(mode: usize, t: usize, rng: &mut Rng) -> Input {
    match mode {
        // minimum values
        0 => build_case(1, 0, 1, 0),

        // maximum candies, minimum people
        1 => build_case(1, 999_999_999, 1, 0),

        // minimum candies, maximum people
        2 => build_case(1, 0, 1, 999),

        // both maxima
        3 => build_case(1, 999_999_999, 1, 999),

        // exact triangular number for small n
        4 => {
            let n = 4;
            let candies = 10; // 1+2+3+4
            build_case(candies, 0, n, 0)
        }

        // one less than triangular
        5 => {
            let n = 4;
            let candies = 9;
            build_case(candies, 0, n, 0)
        }

        // one more than triangular
        6 => {
            let n = 4;
            let candies = 11;
            build_case(candies, 0, n, 0)
        }

        // many full rounds-ish with single person
        7 => {
            let candies = 1_000_000_000;
            build_case(candies, 0, 1, 0)
        }

        // n near upper bound, candies small
        8 => {
            let candies = 2 + (t % 5) as i32;
            let people = 1000;
            build_case(candies, 0, people, 0)
        }

        // random valid, decomposed
        9 => {
            let base_c = rng.gen_range_i32(1, 1_000_000_000);
            let extra_c = rng.gen_range_i32(0, 1_000_000_000 - base_c);
            let base_p = rng.gen_range_i32(1, 1000);
            let extra_p = rng.gen_range_i32(0, 1000 - base_p);
            build_case(base_c, extra_c, base_p, extra_p)
        }

        // candies equal to num_people
        _ => {
            let people = rng.gen_range_i32(1, 1000);
            build_case(people, 0, people, 0)
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
    let total = 200usize;
    let modes = 11usize;

    for t in 0..total {
        let case = if t < 120 {
            adversarial_case(t % modes, t, &mut rng)
        } else {
            let mode = (rng.gen_range_u32(0, (modes - 1) as u32)) as usize;
            adversarial_case(mode, t, &mut rng)
        };

        println!(
            "{{\"candies\":{},\"num_people\":{}}}",
            case.candies, case.num_people
        );
    }
}