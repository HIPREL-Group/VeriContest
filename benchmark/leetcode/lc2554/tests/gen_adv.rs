use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    banned: Vec<i32>,
    n: i32,
    max_sum: i32,
) -> (result: (Vec<i32>, i32, i32))
    requires
        1 <= banned.len() <= 10_000,
        1 <= n <= 10_000,
        1 <= max_sum <= 1_000_000_000,
        forall |i: int| 0 <= i < banned.len() ==> 1 <= #[trigger] banned[i] <= 10_000,
    ensures
        1 <= result.0.len() <= 10_000,
        1 <= result.1 <= 10_000,
        1 <= result.2 <= 1_000_000_000,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 10_000,
{
    (banned, n, max_sum)
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

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
}

fn build_banned(rng: &mut Rng, len: usize, vmin: i32, vmax: i32) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i32(vmin, vmax));
    }
    v
}

fn make_case(mode: usize, t: usize, rng: &mut Rng) -> (Vec<i32>, i32, i32) {
    match mode {
        0 => {
            // small n, small maxSum
            let n = rng.gen_range_i32(1, 10);
            let max_sum = rng.gen_range_i32(1, 20);
            let len = rng.gen_range_usize(1, 5);
            let banned = build_banned(rng, len, 1, 10);
            (banned, n, max_sum)
        }
        1 => {
            // n = 1
            let len = rng.gen_range_usize(1, 100);
            let banned = build_banned(rng, len, 1, 10_000);
            let max_sum = rng.gen_range_i32(1, 1_000_000_000);
            (banned, 1, max_sum)
        }
        2 => {
            // n = 10000, all banned
            let n = 10_000;
            let mut banned: Vec<i32> = Vec::with_capacity(10_000);
            for i in 1..=10_000 {
                banned.push(i as i32);
            }
            let max_sum = rng.gen_range_i32(1, 1_000_000_000);
            (banned, n, max_sum)
        }
        3 => {
            // large n, large maxSum (enough to take all)
            let n = 10_000;
            let len = rng.gen_range_usize(1, 50);
            let banned = build_banned(rng, len, 1, 10_000);
            (banned, n, 1_000_000_000)
        }
        4 => {
            // maxSum = 1 (only take 1 if not banned)
            let n = rng.gen_range_i32(1, 10_000);
            let len = rng.gen_range_usize(1, 20);
            let banned = build_banned(rng, len, 1, 10_000);
            (banned, n, 1)
        }
        5 => {
            // duplicates in banned
            let n = rng.gen_range_i32(5, 100);
            let len = rng.gen_range_usize(10, 100);
            let mut banned: Vec<i32> = Vec::with_capacity(len);
            let val = rng.gen_range_i32(1, n);
            for _ in 0..len {
                banned.push(val);
            }
            let max_sum = rng.gen_range_i32(1, 10_000);
            (banned, n, max_sum)
        }
        6 => {
            // banned values all > n
            let n = rng.gen_range_i32(1, 100);
            let len = rng.gen_range_usize(1, 100);
            let banned = build_banned(rng, len, n + 1, 10_000);
            let max_sum = rng.gen_range_i32(1, 1_000_000_000);
            (banned, n, max_sum)
        }
        7 => {
            // tight maxSum near n*(n+1)/2
            let n = rng.gen_range_i32(10, 200);
            let sum_all = (n as i64 * (n as i64 + 1)) / 2;
            let max_sum = (sum_all.min(1_000_000_000) as i32).max(1);
            let len = rng.gen_range_usize(1, 20);
            let banned = build_banned(rng, len, 1, n);
            (banned, n, max_sum)
        }
        8 => {
            // banned contains 1 (starting element)
            let n = rng.gen_range_i32(10, 1000);
            let mut banned: Vec<i32> = Vec::new();
            banned.push(1);
            let extra = rng.gen_range_usize(0, 30);
            for _ in 0..extra {
                banned.push(rng.gen_range_i32(1, n));
            }
            let max_sum = rng.gen_range_i32(1, 100_000);
            (banned, n, max_sum)
        }
        9 => {
            // maxSum very large
            let n = rng.gen_range_i32(1, 10_000);
            let len = rng.gen_range_usize(1, 100);
            let banned = build_banned(rng, len, 1, 10_000);
            (banned, n, 1_000_000_000)
        }
        _ => {
            // random
            let n = rng.gen_range_i32(1, 10_000);
            let len = rng.gen_range_usize(1, 1000);
            let banned = build_banned(rng, len, 1, 10_000);
            let max_sum = rng.gen_range_i32(1, 1_000_000_000);
            let _ = t;
            (banned, n, max_sum)
        }
    }
}

fn print_json(banned: &[i32], n: i32, max_sum: i32) {
    print!("{{\"banned\":[");
    for i in 0..banned.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", banned[i]);
    }
    println!("],\"n\":{},\"max_sum\":{}}}", n, max_sum);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (banned, n, max_sum) = make_case(mode, t, &mut rng);
        let (banned, n, max_sum) = generate_test_case(banned, n, max_sum);
        print_json(&banned, n, max_sum);
    }
}