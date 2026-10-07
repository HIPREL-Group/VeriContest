use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    fruits: &Vec<i32>,
    baskets: &Vec<i32>,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= fruits.len() <= 100,
        fruits.len() == baskets.len(),
        forall |i: int| 0 <= i < fruits.len() ==> 1 <= #[trigger] fruits[i] <= 1000,
        forall |i: int| 0 <= i < baskets.len() ==> 1 <= #[trigger] baskets[i] <= 1000,
    ensures
        1 <= result.0.len() <= 100,
        result.0.len() == result.1.len(),
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1000,
        forall |i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 1000,
{
    let n = fruits.len();
    let mut f: Vec<i32> = Vec::new();
    let mut b: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == fruits.len(),
            n == baskets.len(),
            1 <= n <= 100,
            i <= n,
            f.len() == i,
            b.len() == i,
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] f[k] <= 1000,
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] b[k] <= 1000,
            forall |k: int| 0 <= k < fruits.len() ==> 1 <= #[trigger] fruits[k] <= 1000,
            forall |k: int| 0 <= k < baskets.len() ==> 1 <= #[trigger] baskets[k] <= 1000,
        decreases n - i,
    {
        f.push(fruits[i]);
        b.push(baskets[i]);
        i += 1;
    }
    (f, b)
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(0x9E3779B97F4A7C15) }
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

fn build_case(rng: &mut Rng, mode: usize) -> (Vec<i32>, Vec<i32>) {
    let n = match mode {
        0 => 1,
        1 => 2,
        2 => 100,
        3 => rng.gen_range_usize(1, 10),
        4 => rng.gen_range_usize(1, 100),
        5 => rng.gen_range_usize(1, 100),
        6 => 100,
        7 => 100,
        8 => rng.gen_range_usize(1, 50),
        9 => rng.gen_range_usize(1, 100),
        _ => rng.gen_range_usize(1, 100),
    };

    let mut fruits = Vec::with_capacity(n);
    let mut baskets = Vec::with_capacity(n);

    match mode {
        0 | 1 => {
            for _ in 0..n {
                fruits.push(rng.gen_range_i32(1, 1000));
                baskets.push(rng.gen_range_i32(1, 1000));
            }
        }
        2 => {
            // all same
            let v = rng.gen_range_i32(1, 1000);
            for _ in 0..n {
                fruits.push(v);
                baskets.push(v);
            }
        }
        3 => {
            // fruits ascending, baskets descending
            for i in 0..n {
                fruits.push(((i + 1) * 10).min(1000) as i32);
                baskets.push(((n - i) * 10).min(1000) as i32);
            }
        }
        4 => {
            // all fruits > all baskets (nothing placed)
            for _ in 0..n {
                fruits.push(rng.gen_range_i32(501, 1000));
                baskets.push(rng.gen_range_i32(1, 500));
            }
        }
        5 => {
            // all fruits <= all baskets (all placed)
            for _ in 0..n {
                fruits.push(rng.gen_range_i32(1, 500));
                baskets.push(rng.gen_range_i32(501, 1000));
            }
        }
        6 => {
            // max values
            for _ in 0..n {
                fruits.push(1000);
                baskets.push(1000);
            }
        }
        7 => {
            // min values
            for _ in 0..n {
                fruits.push(1);
                baskets.push(1);
            }
        }
        8 => {
            // fruits sorted ascending, baskets random
            for i in 0..n {
                fruits.push((((i + 1) * 1000) / n).max(1) as i32);
                baskets.push(rng.gen_range_i32(1, 1000));
            }
        }
        9 => {
            // alternating high/low
            for i in 0..n {
                if i % 2 == 0 {
                    fruits.push(rng.gen_range_i32(1, 100));
                    baskets.push(rng.gen_range_i32(900, 1000));
                } else {
                    fruits.push(rng.gen_range_i32(900, 1000));
                    baskets.push(rng.gen_range_i32(1, 100));
                }
            }
        }
        _ => {
            for _ in 0..n {
                fruits.push(rng.gen_range_i32(1, 1000));
                baskets.push(rng.gen_range_i32(1, 1000));
            }
        }
    }

    (fruits, baskets)
}

fn print_json(fruits: &[i32], baskets: &[i32]) {
    print!("{{\"fruits\":[");
    for i in 0..fruits.len() {
        if i > 0 { print!(","); }
        print!("{}", fruits[i]);
    }
    print!("],\"baskets\":[");
    for i in 0..baskets.len() {
        if i > 0 { print!(","); }
        print!("{}", baskets[i]);
    }
    println!("]}}");
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
        let (fruits, baskets) = build_case(&mut rng, mode);
        let (f, b) = generate_test_case(&fruits, &baskets);
        print_json(&f, &b);
    }
}