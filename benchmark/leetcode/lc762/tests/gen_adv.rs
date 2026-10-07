use vstd::prelude::*;

verus! {

pub fn generate_test_case(left_seed: i32, span_seed: i32, mutation_kind: u8) -> (res: (i32, i32))
    requires
        1 <= left_seed <= 1_000_000,
        0 <= span_seed <= 10_000,
    ensures
        1 <= res.0 <= res.1 <= 1_000_000,
        0 <= res.1 - res.0 <= 10_000,
{
    let bl = left_seed;
    let span = if bl + span_seed > 1_000_000 {
        1_000_000 - bl
    } else {
        span_seed
    };
    let br = bl + span;

    if mutation_kind == 0 {
        (bl, br)
    } else if mutation_kind == 1 {
        (bl, bl)
    } else if mutation_kind == 2 && bl < 1_000_000 {
        (bl, bl + 1)
    } else if mutation_kind == 3 {
        let nl = if bl < 990_000 { 990_000i32 } else { bl };
        (nl, 1_000_000i32)
    } else if mutation_kind == 4 {
        let nr = if 1 + span_seed <= 1_000_000 {
            1 + span_seed
        } else {
            1_000_000i32
        };
        (1i32, nr)
    } else if mutation_kind == 5 && bl > 1 {
        let nl = bl - 1;
        let ns = if nl + span_seed > 1_000_000 {
            1_000_000 - nl
        } else {
            span_seed
        };
        (nl, nl + ns)
    } else if mutation_kind == 6 && bl < 1_000_000 {
        let nl = bl + 1;
        let ns = if nl + span_seed > 1_000_000 {
            1_000_000 - nl
        } else {
            span_seed
        };
        (nl, nl + ns)
    } else if mutation_kind == 7 {
        let hs = span / 2;
        (bl, bl + hs)
    } else if mutation_kind == 8 {
        let ms = if 1_000_000 - bl < 10_000 {
            1_000_000 - bl
        } else {
            10_000i32
        };
        (bl, bl + ms)
    } else {
        (bl, br)
    }
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
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }

    fn gen_u8(&mut self) -> u8 {
        (self.next_u64() % 256) as u8
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
    let left_seeds: Vec<i32> = vec![
        1, 2, 3, 10, 100, 1000, 10_000, 100_000, 500_000, 990_000, 999_990, 1_000_000,
    ];
    let span_seeds: Vec<i32> = vec![0, 1, 2, 5, 10, 100, 1000, 5000, 10_000];

    let total = 200usize;
    for t in 0..total {
        let (ls, ss, mk) = if t < 80 {
            let li = t % left_seeds.len();
            let si = (t / 8) % span_seeds.len();
            (left_seeds[li], span_seeds[si], (t % 10) as u8)
        } else {
            let ls = rng.gen_range_i32(1, 1_000_000);
            let ss = rng.gen_range_i32(0, 10_000);
            (ls, ss, rng.gen_u8() % 10)
        };
        let (left, right) = generate_test_case(ls, ss, mk);
        println!("{{\"left\": {}, \"right\": {}}}", left, right);
    }
}
