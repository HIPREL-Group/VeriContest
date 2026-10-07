use vstd::prelude::*;

verus! {

pub fn generate_test_case(l_val: i32, r_val: i32) -> (res: (i32, i32))
    requires
        1 <= l_val,
        l_val <= r_val,
        r_val <= 10_000_000,
    ensures
        res.0 == l_val,
        res.1 == r_val,
        1 <= res.0 as int,
        res.0 as int <= res.1 as int,
        res.1 as int <= 10_000_000,
{
    (l_val, r_val)
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

fn pick(mode: usize, rng: &mut Rng) -> (i32, i32) {
    match mode {
        0 => (1, 1),
        1 => (1, 2),
        2 => (1, 3),
        3 => (2, 3),
        4 => (2, 4),
        5 => (10_000_000, 10_000_000),
        6 => (9_999_999, 10_000_000),
        7 => {
            let l = rng.gen_range_i32(1, 10);
            let r = rng.gen_range_i32(l, 10);
            (l, r)
        }
        8 => {
            let l = rng.gen_range_i32(1, 100);
            let r = rng.gen_range_i32(l, l + 2);
            (l, r.min(10_000_000))
        }
        9 => {
            let l = rng.gen_range_i32(1, 10_000_000);
            (l, l)
        }
        10 => {
            let l = rng.gen_range_i32(4, 10_000_000);
            let r = rng.gen_range_i32(l, 10_000_000);
            (l, r)
        }
        11 => {
            let x = rng.gen_range_i32(1, 5_000_000);
            (2 * x, 2 * x)
        }
        12 => {
            let p = rng.gen_range_i32(2, 3162);
            let q = p * p;
            (q, q)
        }
        _ => {
            let l = rng.gen_range_i32(1, 10_000_000);
            let r = rng.gen_range_i32(l, 10_000_000);
            (l, r)
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 14usize;
    let total = 220usize;

    for t in 0..total {
        let mode = if t < modes { t } else { (rng.next_u64() as usize) % modes };
        let (l, r) = pick(mode, &mut rng);
        let (l2, r2) = generate_test_case(l, r);
        println!("{{\"l\": {}, \"r\": {}}}", l2, r2);
    }
}