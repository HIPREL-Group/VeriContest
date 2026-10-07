use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (stones: Vec<i32>)
    requires
        2 <= values.len() <= 100_000,
        forall |i: int| 0 <= i < values.len() ==> -10_000 <= #[trigger] values[i] <= 10_000,
    ensures
        2 <= stones.len() <= 100_000,
        forall |i: int| 0 <= i < stones.len() ==> -10_000 <= #[trigger] stones[i] <= 10_000,
{
    let n = values.len();
    let mut stones: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            2 <= n <= 100_000,
            0 <= i <= n,
            stones.len() == i,
            forall |k: int| 0 <= k < values.len() ==> -10_000 <= #[trigger] values[k] <= 10_000,
            forall |k: int| 0 <= k < i as int ==> stones[k] == values[k],
            forall |k: int| 0 <= k < stones.len() ==> -10_000 <= #[trigger] stones[k] <= 10_000,
        decreases n - i,
    {
        stones.push(values[i]);
        i = i + 1;
    }
    stones
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
    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build(n: usize, mode: usize, rng: &mut Rng) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            for _ in 0..n { v.push(rng.gen_i32(-10_000, 10_000)); }
        }
        1 => {
            for _ in 0..n { v.push(10_000); }
        }
        2 => {
            for _ in 0..n { v.push(-10_000); }
        }
        3 => {
            for i in 0..n { v.push(if i % 2 == 0 { 10_000 } else { -10_000 }); }
        }
        4 => {
            for _ in 0..n { v.push(0); }
        }
        5 => {
            for i in 0..n { v.push(if i % 2 == 0 { 1 } else { -1 }); }
        }
        6 => {
            for _ in 0..n { v.push(rng.gen_i32(-5, 5)); }
        }
        7 => {
            for i in 0..n { v.push(if i == 0 { 10_000 } else { rng.gen_i32(-10_000, 10_000) }); }
        }
        8 => {
            for i in 0..n { v.push(if i == n-1 { -10_000 } else { rng.gen_i32(-10_000, 10_000) }); }
        }
        9 => {
            for i in 0..n {
                let x = (i as i32) - (n as i32 / 2);
                let clamped = if x > 10_000 { 10_000 } else if x < -10_000 { -10_000 } else { x };
                v.push(clamped);
            }
        }
        _ => {
            for _ in 0..n { v.push(rng.gen_i32(-100, 100)); }
        }
    }
    v
}

fn print_json(stones: &[i32]) {
    print!("{{\"stones\":[");
    for i in 0..stones.len() {
        if i > 0 { print!(","); }
        print!("{}", stones[i]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match t % 7 {
            0 => 2,
            1 => 3,
            2 => rng.gen_usize(2, 20),
            3 => rng.gen_usize(20, 200),
            4 => rng.gen_usize(200, 2000),
            5 => rng.gen_usize(2, 100),
            _ => rng.gen_usize(2, 500),
        };
        let values = build(n, mode, &mut rng);
        let stones = generate_test_case(&values);
        print_json(&stones);
    }
}