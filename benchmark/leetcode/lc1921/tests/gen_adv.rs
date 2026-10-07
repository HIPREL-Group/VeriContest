use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    dist: Vec<i32>,
    speed: Vec<i32>,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        dist.len() == speed.len(),
        1 <= dist.len() <= 100_000,
        forall |i: int| 0 <= i < dist.len() ==> 1 <= #[trigger] dist[i] <= 100_000,
        forall |i: int| 0 <= i < speed.len() ==> 1 <= #[trigger] speed[i] <= 100_000,
    ensures
        result.0.len() == result.1.len(),
        1 <= result.0.len() <= 100_000,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100_000,
        forall |i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 100_000,
{
    (dist, speed)
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
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build_case(dist: Vec<i32>, speed: Vec<i32>) -> (Vec<i32>, Vec<i32>) {
    // Validate bounds
    assert!(dist.len() == speed.len());
    assert!(!dist.is_empty() && dist.len() <= 100_000);
    for &d in &dist {
        assert!(d >= 1 && d <= 100_000);
    }
    for &s in &speed {
        assert!(s >= 1 && s <= 100_000);
    }
    generate_test_case(dist, speed)
}

fn print_json(d: &[i32], s: &[i32]) {
    print!("{{\"dist\":[");
    for i in 0..d.len() {
        if i > 0 { print!(","); }
        print!("{}", d[i]);
    }
    print!("],\"speed\":[");
    for i in 0..s.len() {
        if i > 0 { print!(","); }
        print!("{}", s[i]);
    }
    println!("]}}");
}

fn adversarial_case(rng: &mut Rng, mode: usize) -> (Vec<i32>, Vec<i32>) {
    match mode {
        0 => {
            // minimum size
            (vec![1], vec![1])
        }
        1 => {
            // all distance 1, speed 1 (loses fast)
            let n = rng.gen_range_usize(1, 100);
            let d = vec![1i32; n];
            let s = vec![1i32; n];
            (d, s)
        }
        2 => {
            // all at max distance, min speed
            let n = rng.gen_range_usize(1, 1000);
            let d = vec![100_000i32; n];
            let s = vec![1i32; n];
            (d, s)
        }
        3 => {
            // all at min distance, max speed
            let n = rng.gen_range_usize(1, 100);
            let d = vec![1i32; n];
            let s = vec![100_000i32; n];
            (d, s)
        }
        4 => {
            // increasing distances
            let n = rng.gen_range_usize(10, 1000);
            let mut d = Vec::with_capacity(n);
            let mut s = Vec::with_capacity(n);
            for i in 0..n {
                d.push(((i as i32 % 100_000) + 1).max(1));
                s.push(1);
            }
            (d, s)
        }
        5 => {
            // same arrival time edge case: d=i+1 s=1, monster i arrives at time i+1
            let n = rng.gen_range_usize(1, 500);
            let mut d = Vec::with_capacity(n);
            let mut s = Vec::with_capacity(n);
            for i in 0..n {
                let di = ((i as i32) + 1).min(100_000).max(1);
                d.push(di);
                s.push(1);
            }
            (d, s)
        }
        6 => {
            // tight: arrival exactly at i
            let n = rng.gen_range_usize(2, 100);
            let mut d = Vec::with_capacity(n);
            let mut s = Vec::with_capacity(n);
            for i in 0..n {
                let di = (i as i32).max(1).min(100_000);
                d.push(di);
                s.push(1);
            }
            (d, s)
        }
        7 => {
            // big n, random
            let n = 100_000;
            let mut d = Vec::with_capacity(n);
            let mut s = Vec::with_capacity(n);
            for _ in 0..n {
                d.push(rng.gen_range_i32(1, 100_000));
                s.push(rng.gen_range_i32(1, 100_000));
            }
            (d, s)
        }
        8 => {
            // ceiling edge: d=1, various speeds => arrival=1
            let n = rng.gen_range_usize(1, 200);
            let mut d = Vec::with_capacity(n);
            let mut s = Vec::with_capacity(n);
            for _ in 0..n {
                d.push(1);
                s.push(rng.gen_range_i32(1, 100_000));
            }
            (d, s)
        }
        9 => {
            // all same arrival time
            let n = rng.gen_range_usize(1, 200);
            let d = vec![10i32; n];
            let s = vec![1i32; n];
            (d, s)
        }
        _ => {
            let n = rng.gen_range_usize(1, 2000);
            let mut d = Vec::with_capacity(n);
            let mut s = Vec::with_capacity(n);
            for _ in 0..n {
                d.push(rng.gen_range_i32(1, 100_000));
                s.push(rng.gen_range_i32(1, 100_000));
            }
            (d, s)
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };
    let mut rng = Rng::new(seed);

    let total = 200;
    let modes = 11;
    for t in 0..total {
        let mode = t % modes;
        let (d, s) = adversarial_case(&mut rng, mode);
        let (d2, s2) = build_case(d, s);
        print_json(&d2, &s2);
    }
}