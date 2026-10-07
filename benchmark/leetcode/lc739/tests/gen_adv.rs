use vstd::prelude::*;

verus! {

pub fn generate_test_case(raw: &Vec<i32>) -> (temps: Vec<i32>)
    requires
        1 <= raw.len() <= 100_000,
    ensures
        1 <= temps.len() <= 100_000,
        temps.len() == raw.len(),
        forall |i: int| 0 <= i < temps.len() ==> 30 <= #[trigger] temps[i] <= 100,
{
    let mut temps: Vec<i32> = Vec::new();
    let n = raw.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == raw.len(),
            1 <= n <= 100_000,
            temps.len() == i,
            forall |k: int| 0 <= k < i as int ==> 30 <= #[trigger] temps[k] <= 100,
        decreases n - i,
    {
        let v = raw[i];
        let clamped: i32 = if v < 30 {
            30
        } else if v > 100 {
            100
        } else {
            v
        };
        temps.push(clamped);
        i = i + 1;
    }
    temps
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

fn make_mode(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            // single element
            vec![rng.gen_range_i32(30, 100)]
        }
        1 => {
            // strictly increasing
            let n = rng.gen_range_usize(2, 100);
            let start = rng.gen_range_i32(30, 100 - (n as i32 - 1).min(70));
            let mut v = Vec::new();
            let mut cur = start;
            for _ in 0..n {
                v.push(cur);
                if cur < 100 { cur += 1; }
            }
            v
        }
        2 => {
            // strictly decreasing
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::new();
            let mut cur: i32 = 100;
            for _ in 0..n {
                v.push(cur);
                if cur > 30 { cur -= 1; }
            }
            v
        }
        3 => {
            // all equal
            let n = rng.gen_range_usize(1, 1000);
            let val = rng.gen_range_i32(30, 100);
            vec![val; n]
        }
        4 => {
            // all 30
            let n = rng.gen_range_usize(1, 1000);
            vec![30; n]
        }
        5 => {
            // all 100
            let n = rng.gen_range_usize(1, 1000);
            vec![100; n]
        }
        6 => {
            // large size
            let n = 100_000;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(30, 100));
            }
            v
        }
        7 => {
            // large strictly decreasing pattern (worst case for stack)
            let n = 100_000;
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                let x = 100 - ((i as i32) % 71);
                v.push(x);
            }
            v
        }
        8 => {
            // example case
            vec![73,74,75,71,69,72,76,73]
        }
        9 => {
            // zigzag
            let n = rng.gen_range_usize(2, 500);
            let mut v = Vec::new();
            for i in 0..n {
                v.push(if i % 2 == 0 { 50 } else { 60 });
            }
            v
        }
        10 => {
            // plateau then jump
            let n = rng.gen_range_usize(2, 200);
            let plateau = rng.gen_range_i32(30, 99);
            let mut v = vec![plateau; n - 1];
            v.push(plateau + 1);
            v
        }
        _ => {
            let n = rng.gen_range_usize(1, 200);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(30, 100));
            }
            v
        }
    }
}

fn print_json(temps: &[i32]) {
    print!("{{\"temperatures\":[");
    for i in 0..temps.len() {
        if i > 0 { print!(","); }
        print!("{}", temps[i]);
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
    let modes = 12usize;
    let total = 200usize;
    for t in 0..total {
        let mode = t % modes;
        let raw = make_mode(&mut rng, mode, t);
        if raw.is_empty() {
            continue;
        }
        if raw.len() > 100_000 {
            continue;
        }
        let temps = generate_test_case(&raw);
        print_json(&temps);
    }
}