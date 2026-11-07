use vstd::prelude::*;

verus! {

pub open spec fn is_no_zero_spec(x: int) -> bool
    decreases x,
{
    if x <= 0 {
        false
    } else if x < 10 {
        true
    } else {
        x % 10 != 0 && is_no_zero_spec(x / 10)
    }
}

pub fn generate_test_case(n: i32) -> (result: i32)
    requires
        2 <= n <= 10000,
    ensures
        2 <= result <= 10000,
        result == n,
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
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + ((self.next_u64() % span) as i32)
    }
}

fn adversarial(mode: usize, rng: &mut Rng) -> i32 {
    match mode {
        0 => 2,
        1 => 10000,
        2 => 9999,
        3 => 10,
        4 => 100,
        5 => 1000,
        6 => 11,
        7 => 101,
        8 => 1001,
        9 => rng.gen_range_i32(2, 10000),
        _ => rng.gen_range_i32(2, 100),
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
        let mode = t % modes;
        let n = adversarial(mode, &mut rng);
        let x = generate_test_case(n);
        println!("{{\"x\":{}}}", x);
    }
}