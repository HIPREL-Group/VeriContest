use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    k_val: i32,
    fillers: &Vec<i32>,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= n <= 100_000,
        1 <= k_val,
        k_val as int <= n as int - 1,
        fillers.len() == n,
        forall|i: int| 0 <= i < fillers.len() ==> -1000 <= #[trigger] fillers[i] <= 1000,
    ensures
        1 <= result.0.len() <= 100_000,
        forall|i: int| 0 <= i < result.0.len() ==> -1000 <= #[trigger] result.0[i] <= 1000,
        1 <= result.1,
        result.1 as int <= result.0.len() as int - 1,
        result.0.len() == n,
        result.1 == k_val,
{
    let mut energy: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            energy.len() == i,
            fillers.len() == n,
            forall|j: int| 0 <= j < i as int ==> -1000 <= #[trigger] energy[j] <= 1000,
            forall|j: int| 0 <= j < fillers.len() ==> -1000 <= #[trigger] fillers[j] <= 1000,
        decreases n - i,
    {
        energy.push(fillers[i]);
        i = i + 1;
    }
    (energy, k_val)
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

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn make_fillers(rng: &mut Rng, n: usize, mode: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        let x = match mode {
            0 => rng.gen_range_i32(-1000, 1000),
            1 => 1000,
            2 => -1000,
            3 => 0,
            4 => if i % 2 == 0 { 1000 } else { -1000 },
            5 => rng.gen_range_i32(1, 1000),
            6 => rng.gen_range_i32(-1000, -1),
            7 => {
                if i == n / 2 { 1000 } else { rng.gen_range_i32(-1000, -900) }
            }
            8 => {
                if i == 0 { -1000 } else { rng.gen_range_i32(900, 1000) }
            }
            9 => {
                let v = ((i as i32) % 21) - 10;
                v * 100
            }
            _ => rng.gen_range_i32(-1000, 1000),
        };
        v.push(x);
    }
    v
}

fn print_json(energy: &[i32], k: i32) {
    print!("{{\"energy\":[");
    for i in 0..energy.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", energy[i]);
    }
    println!("],\"k\":{}}}", k);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let modes = 10usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        // n must be >= 2 because k >= 1 and k <= n-1
        let n: usize = match mode {
            0 => rng.gen_range_usize(2, 20),
            1 => 100_000,
            2 => 2,
            3 => rng.gen_range_usize(2, 100),
            4 => rng.gen_range_usize(50, 500),
            5 => 99_999,
            6 => 1000,
            7 => rng.gen_range_usize(2, 10),
            8 => rng.gen_range_usize(100, 1000),
            _ => rng.gen_range_usize(2, 50_000),
        };

        let max_k = if n >= 2 { n - 1 } else { 1 };
        let k: i32 = match mode % 5 {
            0 => 1,
            1 => max_k as i32,
            2 => ((max_k / 2).max(1)) as i32,
            3 => rng.gen_range_usize(1, max_k) as i32,
            _ => {
                let r = rng.gen_range_usize(1, max_k);
                r as i32
            }
        };

        let fillers = make_fillers(&mut rng, n, mode);
        let (energy, k_out) = generate_test_case(n, k, &fillers);
        print_json(&energy, k_out);
    }
}