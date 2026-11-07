use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    k: usize,
    raw: &Vec<u8>,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= n <= 100,
        k < n,
        raw.len() == n,
        forall|i: int| 0 <= i < raw.len() ==> 1 <= #[trigger] raw[i] <= 100,
    ensures
        1 <= result.0.len() <= 100,
        0 <= result.1 < result.0.len(),
        forall|j: int| 0 <= j < result.0.len() ==> 1 <= #[trigger] result.0[j] <= 100,
{
    let mut tickets: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == raw.len(),
            1 <= n <= 100,
            0 <= i <= n,
            tickets.len() == i,
            forall|j: int| 0 <= j < raw.len() ==> 1 <= #[trigger] raw[j] <= 100,
            forall|j: int| 0 <= j < tickets.len() ==> 1 <= #[trigger] tickets[j] <= 100,
        decreases n - i,
    {
        let v: i32 = raw[i] as i32;
        assert(1 <= raw[i as int] <= 100);
        tickets.push(v);
        i = i + 1;
    }
    (tickets, k as i32)
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
    fn gen_u8(&mut self, lo: u8, hi: u8) -> u8 {
        let span = (hi - lo + 1) as u64;
        (lo as u64 + self.next_u64() % span) as u8
    }
}

fn build_raw(rng: &mut Rng, n: usize, mode: usize, k: usize) -> Vec<u8> {
    let mut v: Vec<u8> = Vec::with_capacity(n);
    match mode {
        0 => {
            for _ in 0..n { v.push(1); }
        }
        1 => {
            for _ in 0..n { v.push(100); }
        }
        2 => {
            for i in 0..n {
                if i == k { v.push(100); } else { v.push(1); }
            }
        }
        3 => {
            for i in 0..n {
                if i == k { v.push(1); } else { v.push(100); }
            }
        }
        4 => {
            for _ in 0..n { v.push(rng.gen_u8(1, 100)); }
        }
        5 => {
            for i in 0..n {
                v.push(((i % 100) + 1) as u8);
            }
        }
        6 => {
            for i in 0..n {
                v.push((((n - i) % 100) + 1) as u8);
            }
        }
        7 => {
            for i in 0..n {
                if i < k { v.push(rng.gen_u8(1, 50)); }
                else if i == k { v.push(rng.gen_u8(1, 100)); }
                else { v.push(rng.gen_u8(50, 100)); }
            }
        }
        8 => {
            for _ in 0..n { v.push(rng.gen_u8(1, 5)); }
        }
        9 => {
            for _ in 0..n { v.push(rng.gen_u8(95, 100)); }
        }
        _ => {
            for _ in 0..n { v.push(rng.gen_u8(1, 100)); }
        }
    }
    v
}

fn print_json(tickets: &[i32], k: i32) {
    print!("{{\"tickets\":[");
    for i in 0..tickets.len() {
        if i > 0 { print!(","); }
        print!("{}", tickets[i]);
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
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => 1,
            1 => 100,
            2 => rng.gen_usize(1, 100),
            3 => rng.gen_usize(2, 100),
            4 => rng.gen_usize(1, 100),
            5 => 50,
            6 => 75,
            7 => rng.gen_usize(3, 100),
            8 => 100,
            _ => rng.gen_usize(1, 100),
        };
        let n = if n < 1 { 1 } else if n > 100 { 100 } else { n };
        let k = rng.gen_usize(0, n - 1);
        let raw = build_raw(&mut rng, n, mode, k);
        let (tickets, kk) = generate_test_case(n, k, &raw);
        print_json(&tickets, kk);
    }
}