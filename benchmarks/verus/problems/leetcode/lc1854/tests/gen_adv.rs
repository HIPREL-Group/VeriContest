use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    births: &Vec<i32>,
    deaths: &Vec<i32>,
) -> (logs: Vec<Vec<i32>>)
    requires
        births.len() == deaths.len(),
        1 <= births.len() <= 100,
        forall|i: int| 0 <= i < births.len() ==>
            1950 <= #[trigger] births[i] && births[i] < deaths[i] && deaths[i] <= 2050,
    ensures
        1 <= logs.len() <= 100,
        forall|i: int|
            0 <= i < logs.len() ==> (#[trigger] logs[i].len() == 2 && 1950 <= logs[i][0]
                && logs[i][0] < logs[i][1] && logs[i][1] <= 2050),
{
    let n = births.len();
    let mut logs: Vec<Vec<i32>> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            n == births.len(),
            n == deaths.len(),
            1 <= n <= 100,
            0 <= k <= n,
            logs.len() == k,
            forall|i: int| 0 <= i < births.len() ==>
                1950 <= #[trigger] births[i] && births[i] < deaths[i] && deaths[i] <= 2050,
            forall|i: int| 0 <= i < k as int ==>
                (#[trigger] logs[i].len() == 2 && logs[i][0] == births[i] && logs[i][1] == deaths[i]),
        decreases n - k,
    {
        let mut pair: Vec<i32> = Vec::new();
        pair.push(births[k]);
        pair.push(deaths[k]);
        assert(pair.len() == 2);
        assert(pair[0] == births[k as int]);
        assert(pair[1] == deaths[k as int]);
        logs.push(pair);
        k = k + 1;
    }
    logs
}

}

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

fn build_case(rng: &mut Rng, mode: usize, t: usize) -> (Vec<i32>, Vec<i32>) {
    let n = match mode {
        0 => 1,
        1 => 100,
        2 => 2,
        3 => rng.gen_range_usize(1, 100),
        4 => 100,
        5 => 50,
        6 => 100,
        7 => rng.gen_range_usize(1, 10),
        8 => 100,
        9 => rng.gen_range_usize(1, 100),
        _ => rng.gen_range_usize(1, 100),
    };
    let mut b = Vec::with_capacity(n);
    let mut d = Vec::with_capacity(n);
    for _ in 0..n {
        let (bi, di) = match mode {
            0 => (1950i32, 2050i32),
            1 => (1950i32, 1951i32),
            2 => (2049i32, 2050i32),
            3 => {
                let bb = rng.gen_range_i32(1950, 2049);
                let dd = rng.gen_range_i32(bb + 1, 2050);
                (bb, dd)
            }
            4 => {
                let bb = 1950 + (t as i32 % 100);
                let dd = bb + 1;
                (bb, dd)
            }
            5 => {
                let bb = rng.gen_range_i32(1990, 2010);
                let dd = rng.gen_range_i32(bb + 1, 2050);
                (bb, dd)
            }
            6 => {
                let bb = rng.gen_range_i32(1950, 2049);
                (bb, 2050)
            }
            7 => {
                let bb = rng.gen_range_i32(1950, 2049);
                let dd = bb + 1;
                (bb, dd)
            }
            8 => {
                let bb = 2000i32;
                let dd = rng.gen_range_i32(2001, 2050);
                (bb, dd)
            }
            9 => {
                let bb = rng.gen_range_i32(1950, 2049);
                let dd = rng.gen_range_i32(bb + 1, (bb + 5).min(2050));
                (bb, dd)
            }
            _ => {
                let bb = rng.gen_range_i32(1950, 2049);
                let dd = rng.gen_range_i32(bb + 1, 2050);
                (bb, dd)
            }
        };
        b.push(bi);
        d.push(di);
    }
    (b, d)
}

fn print_json(logs: &[Vec<i32>]) {
    print!("{{\"logs\":[");
    for i in 0..logs.len() {
        if i > 0 { print!(","); }
        print!("[{},{}]", logs[i][0], logs[i][1]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;
    for t in 0..total {
        let mode = t % modes;
        let (b, d) = build_case(&mut rng, mode, t);
        let logs = generate_test_case(&b, &d);
        print_json(&logs);
    }
}