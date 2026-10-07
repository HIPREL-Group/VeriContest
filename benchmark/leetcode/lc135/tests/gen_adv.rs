use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, vals: &Vec<i32>) -> (ratings: Vec<i32>)
    requires
        1 <= n <= 20_000,
        vals.len() == n,
        forall|i: int| 0 <= i < vals.len() ==> 0 <= #[trigger] vals[i] <= 20_000,
    ensures
        1 <= ratings.len() <= 20_000,
        forall|i: int| 0 <= i < ratings.len() ==> 0 <= #[trigger] ratings[i] <= 20_000,
{
    let mut ratings: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            1 <= n <= 20_000,
            vals.len() == n,
            ratings.len() == i,
            forall|k: int| 0 <= k < vals.len() ==> 0 <= #[trigger] vals[k] <= 20_000,
            forall|k: int| 0 <= k < ratings.len() ==> 0 <= #[trigger] ratings[k] <= 20_000,
            forall|k: int| 0 <= k < ratings.len() ==> #[trigger] ratings[k] == vals[k],
        decreases n - i,
    {
        ratings.push(vals[i]);
        i = i + 1;
    }
    ratings
}

} // verus!

struct Rng { state: u64 }

impl Rng {
    fn new(seed: u64) -> Self { Self { state: seed.wrapping_add(1) } }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build(n: usize, vals: Vec<i32>) -> Vec<i32> {
    generate_test_case(n, &vals)
}

fn mode_random(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n { v.push(rng.gen_i32(0, 20_000)); }
    v
}

fn mode_all_same(rng: &mut Rng, n: usize) -> Vec<i32> {
    let x = rng.gen_i32(0, 20_000);
    vec![x; n]
}

fn mode_strict_increasing(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n { v.push((i % 20_001) as i32); }
    v
}

fn mode_strict_decreasing(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n { v.push(((n - 1 - i) % 20_001) as i32); }
    v
}

fn mode_mountain(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    let half = n / 2;
    for i in 0..n {
        let r = if i <= half { i } else { n - 1 - i };
        v.push((r % 20_001) as i32);
    }
    v
}

fn mode_valley(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    let half = n / 2;
    for i in 0..n {
        let r = if i <= half { half - i } else { i - half };
        v.push((r % 20_001) as i32);
    }
    v
}

fn mode_plateaus(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    let mut i = 0;
    while i < n {
        let len = rng.gen_usize(1, 5).min(n - i);
        let val = rng.gen_i32(0, 20_000);
        for _ in 0..len { v.push(val); }
        i += len;
    }
    v
}

fn mode_zigzag(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n { v.push(if i % 2 == 0 { 0 } else { 20_000 }); }
    v
}

fn mode_small_range(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n { v.push(rng.gen_i32(0, 2)); }
    v
}

fn mode_extremes(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(if rng.next_u64() % 2 == 0 { 0 } else { 20_000 });
    }
    v
}

fn print_json(r: &[i32]) {
    print!("{{\"ratings\":[");
    for i in 0..r.len() {
        if i > 0 { print!(","); }
        print!("{}", r[i]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);

    let total = 200usize;
    for t in 0..total {
        let mode = t % 10;
        let n: usize = match t {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => 20_000,
            _ => match mode {
                0 => rng.gen_usize(1, 200),
                1 => rng.gen_usize(1, 500),
                2 => rng.gen_usize(2, 300),
                3 => rng.gen_usize(2, 300),
                4 => rng.gen_usize(3, 400),
                5 => rng.gen_usize(3, 400),
                6 => rng.gen_usize(5, 500),
                7 => rng.gen_usize(2, 200),
                8 => rng.gen_usize(1, 100),
                _ => rng.gen_usize(2, 1000),
            }
        };
        let n = n.max(1).min(20_000);
        let vals = match mode {
            0 => mode_random(&mut rng, n),
            1 => mode_all_same(&mut rng, n),
            2 => mode_strict_increasing(n),
            3 => mode_strict_decreasing(n),
            4 => mode_mountain(n),
            5 => mode_valley(n),
            6 => mode_plateaus(&mut rng, n),
            7 => mode_zigzag(n),
            8 => mode_small_range(&mut rng, n),
            _ => mode_extremes(&mut rng, n),
        };
        let r = build(n, vals);
        print_json(&r);
    }
}