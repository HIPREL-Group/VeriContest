use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (res: Vec<i32>)
    requires
        1 <= values.len() <= 10000,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1_000_000_000,
    ensures
        1 <= res.len() <= 10000,
        res.len() == values.len(),
        forall|i: int| 0 <= i < res.len() ==> 1 <= #[trigger] res[i] <= 1_000_000_000,
{
    let n = values.len();
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            1 <= n <= 10000,
            0 <= i <= n,
            res.len() == i,
            forall|k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 1_000_000_000,
            forall|k: int| 0 <= k < i as int ==> 1 <= #[trigger] res[k] <= 1_000_000_000,
            forall|k: int| 0 <= k < i as int ==> res[k] == values[k],
        decreases n - i,
    {
        res.push(values[i]);
        i = i + 1;
    }
    res
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
    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn build(values: Vec<i32>) -> Vec<i32> {
    generate_test_case(&values)
}

fn emit(a: &[i32]) {
    print!("{{\"a\":[");
    for i in 0..a.len() {
        if i > 0 { print!(","); }
        print!("{}", a[i]);
    }
    println!("]}}");
}

fn mode_random(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_i32(1, 1_000_000_000));
    }
    v
}

fn mode_all_ones(n: usize) -> Vec<i32> {
    vec![1i32; n]
}

fn mode_increasing_doubles(n: usize) -> Vec<i32> {
    // every element divides the next: 1, 2, 4, 8, ... capped
    let mut v = Vec::with_capacity(n);
    let mut cur: i64 = 1;
    for _ in 0..n {
        v.push(cur as i32);
        cur = cur.saturating_mul(2);
        if cur > 1_000_000_000 { cur = 1_000_000_000; }
    }
    v
}

fn mode_same_value(n: usize, val: i32) -> Vec<i32> {
    vec![val; n]
}

fn mode_max(n: usize) -> Vec<i32> {
    vec![1_000_000_000i32; n]
}

fn mode_alternating(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        v.push(if i % 2 == 0 { 1 } else { 1_000_000_000 });
    }
    v
}

fn mode_small(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_i32(1, 5));
    }
    v
}

fn mode_divisible_chain(rng: &mut Rng, n: usize) -> Vec<i32> {
    // a[i+1] = a[i] * k
    let mut v = Vec::with_capacity(n);
    let mut cur: i64 = rng.gen_i32(1, 10) as i64;
    for _ in 0..n {
        v.push(cur as i32);
        let k = rng.gen_i32(1, 3) as i64;
        cur = cur.saturating_mul(k);
        if cur > 1_000_000_000 || cur < 1 { cur = rng.gen_i32(1, 10) as i64; }
    }
    v
}

fn mode_ones_and_big(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        if rng.next_u64() % 2 == 0 {
            v.push(1);
        } else {
            v.push(rng.gen_i32(1, 1_000_000_000));
        }
    }
    v
}

fn mode_consecutive(n: usize, start: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    let mut cur = start as i64;
    for _ in 0..n {
        if cur < 1 { cur = 1; }
        if cur > 1_000_000_000 { cur = 1_000_000_000; }
        v.push(cur as i32);
        cur += 1;
    }
    v
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);

    let total = 200usize;
    for t in 0..total {
        let mode = t % 10;
        let n = match mode {
            0 => rng.gen_usize(1, 20),
            1 => 1,
            2 => 10000,
            3 => rng.gen_usize(2, 50),
            4 => rng.gen_usize(1, 100),
            5 => 2,
            6 => rng.gen_usize(100, 500),
            7 => rng.gen_usize(2, 30),
            8 => rng.gen_usize(1, 10000),
            _ => rng.gen_usize(1, 200),
        };

        let values = match mode {
            0 => mode_random(&mut rng, n),
            1 => mode_all_ones(n),
            2 => mode_increasing_doubles(n),
            3 => {
                let v = rng.gen_i32(1, 1_000_000_000);
                mode_same_value(n, v)
            }
            4 => mode_max(n),
            5 => mode_alternating(n),
            6 => mode_small(&mut rng, n),
            7 => mode_divisible_chain(&mut rng, n),
            8 => mode_ones_and_big(&mut rng, n),
            _ => {
                let s = rng.gen_i32(1, 1000);
                mode_consecutive(n, s)
            }
        };

        let result = build(values);
        emit(&result);
    }
}