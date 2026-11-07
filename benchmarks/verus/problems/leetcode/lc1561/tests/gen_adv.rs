use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n_thirds: usize,
    values: &Vec<i32>,
) -> (piles: Vec<i32>)
    requires
        1 <= n_thirds <= 33333,
        values.len() == 3 * n_thirds,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 10000,
    ensures
        3 <= piles.len() <= 100000,
        piles.len() % 3 == 0,
        forall|i: int| 0 <= i < piles.len() ==> 1 <= #[trigger] piles[i] <= 10000,
{
    let n: usize = 3 * n_thirds;
    let mut piles: Vec<i32> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            n == 3 * n_thirds,
            1 <= n_thirds <= 33333,
            values.len() == n,
            0 <= i <= n,
            piles.len() == i,
            forall|k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 10000,
            forall|k: int| 0 <= k < i as int ==> #[trigger] piles[k] == values[k],
            forall|k: int| 0 <= k < i as int ==> 1 <= #[trigger] piles[k] <= 10000,
        decreases n - i,
    {
        piles.push(values[i]);
        i = i + 1;
    }

    assert(piles.len() == n);
    assert(n >= 3);
    assert(n <= 99999);
    assert(n % 3 == 0) by {
        assert(n == 3 * n_thirds);
    }

    piles
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
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build(n_thirds: usize, values: Vec<i32>) -> Vec<i32> {
    generate_test_case(n_thirds, &values)
}

fn print_case(piles: &[i32]) {
    print!("{{\"piles\":[");
    for i in 0..piles.len() {
        if i > 0 { print!(","); }
        print!("{}", piles[i]);
    }
    println!("]}}");
}

fn gen_mode(rng: &mut Rng, mode: usize, t: usize) -> (usize, Vec<i32>) {
    let n_thirds: usize = match mode {
        0 => 1,
        1 => 2,
        2 => 33333,
        3 => rng.gen_range_usize(1, 100),
        4 => rng.gen_range_usize(100, 1000),
        5 => rng.gen_range_usize(1000, 10000),
        6 => rng.gen_range_usize(1, 33333),
        7 => 1 + (t % 50),
        8 => 33333,
        9 => rng.gen_range_usize(1, 500),
        _ => rng.gen_range_usize(1, 200),
    };
    let n = 3 * n_thirds;
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            for _ in 0..n { v.push(rng.gen_range_i32(1, 10000)); }
        }
        1 => {
            for _ in 0..n { v.push(1); }
        }
        2 => {
            for _ in 0..n { v.push(10000); }
        }
        3 => {
            let x = rng.gen_range_i32(1, 10000);
            for _ in 0..n { v.push(x); }
        }
        4 => {
            for i in 0..n { v.push(((i % 10000) as i32) + 1); }
        }
        5 => {
            for i in 0..n { v.push(((n - i) % 10000) as i32 + 1); }
        }
        6 => {
            for _ in 0..n {
                if rng.next_u64() % 2 == 0 { v.push(1); } else { v.push(10000); }
            }
        }
        7 => {
            // two values
            let a = rng.gen_range_i32(1, 5000);
            let b = rng.gen_range_i32(5001, 10000);
            for _ in 0..n {
                if rng.next_u64() % 2 == 0 { v.push(a); } else { v.push(b); }
            }
        }
        8 => {
            for i in 0..n { v.push(((i * 7 + 3) % 10000) as i32 + 1); }
        }
        9 => {
            // small range
            for _ in 0..n { v.push(rng.gen_range_i32(1, 5)); }
        }
        _ => {
            for _ in 0..n { v.push(rng.gen_range_i32(1, 10000)); }
        }
    }
    (n_thirds, v)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 200usize;
    for t in 0..total {
        let mode = t % modes;
        let (n_thirds, values) = gen_mode(&mut rng, mode, t);
        let piles = build(n_thirds, values);
        print_case(&piles);
    }
}