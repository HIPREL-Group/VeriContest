use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n_val: i32,
    quantities: Vec<i32>,
) -> (res: (i32, Vec<i32>))
    requires
        1 <= quantities.len() <= n_val <= 100000,
        forall |i: int| 0 <= i < quantities.len() ==> 1 <= #[trigger] quantities[i] <= 100000,
    ensures
        1 <= res.1.len() <= res.0 <= 100000,
        forall |i: int| 0 <= i < res.1.len() ==> 1 <= #[trigger] res.1[i] <= 100000,
{
    (n_val, quantities)
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed }
    }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
}

fn build_case(rng: &mut Rng, mode: usize) -> (i32, Vec<i32>) {
    match mode {
        0 => {
            // Minimal: m=1, n=1
            (1i32, vec![rng.gen_range_i32(1, 100000)])
        }
        1 => {
            // m=1, large quantity
            let n = rng.gen_range_i32(1, 100000);
            (n, vec![100000])
        }
        2 => {
            // m=n, all ones
            let n = rng.gen_range_i32(1, 100) as usize;
            let q: Vec<i32> = (0..n).map(|_| 1i32).collect();
            (n as i32, q)
        }
        3 => {
            // m=n, all at max
            let n = rng.gen_range_i32(1, 1000) as usize;
            let q: Vec<i32> = (0..n).map(|_| 100000i32).collect();
            (n as i32, q)
        }
        4 => {
            // n much larger than sum
            let m = rng.gen_range_usize(1, 50);
            let q: Vec<i32> = (0..m).map(|_| rng.gen_range_i32(1, 10)).collect();
            let sum: i32 = q.iter().sum();
            let n = std::cmp::max(m as i32, std::cmp::min(100000, sum * 10));
            (n, q)
        }
        5 => {
            // Example 1
            (6, vec![11, 6])
        }
        6 => {
            // Example 2
            (7, vec![15, 10, 10])
        }
        7 => {
            // Example 3
            (1, vec![100000])
        }
        8 => {
            // Large m with varying quantities
            let m = rng.gen_range_usize(100, 1000);
            let q: Vec<i32> = (0..m).map(|_| rng.gen_range_i32(1, 100000)).collect();
            let n = rng.gen_range_i32(m as i32, 100000);
            (n, q)
        }
        9 => {
            // m = n case
            let m = rng.gen_range_usize(1, 100000);
            let q: Vec<i32> = (0..m).map(|_| rng.gen_range_i32(1, 100000)).collect();
            (m as i32, q)
        }
        _ => {
            // Random
            let m = rng.gen_range_usize(1, 500);
            let q: Vec<i32> = (0..m).map(|_| rng.gen_range_i32(1, 100000)).collect();
            let n = rng.gen_range_i32(m as i32, 100000);
            (n, q)
        }
    }
}

fn compute_x(n: i32, quantities: &Vec<i32>) -> i32 {
    // binary search for minimum x
    let mut lo: i64 = 1;
    let mut hi: i64 = 100000;
    while lo < hi {
        let mid = (lo + hi) / 2;
        let mut needed: i64 = 0;
        for &q in quantities {
            needed += (q as i64 + mid - 1) / mid;
        }
        if needed <= n as i64 {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }
    lo as i32
}

fn print_json(n: i32, q: &Vec<i32>) {
    print!("{{\"n\":{},\"quantities\":[", n);
    for i in 0..q.len() {
        if i > 0 { print!(","); }
        print!("{}", q[i]);
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
        let (n, q) = build_case(&mut rng, mode);
        // sanity clamp
        if q.is_empty() || n < q.len() as i32 || n > 100000 {
            continue;
        }
        let mut valid = true;
        for &x in &q {
            if x < 1 || x > 100000 { valid = false; break; }
        }
        if !valid { continue; }
        let (n_out, q_out) = generate_test_case(n, q);
        let _x = compute_x(n_out, &q_out);
        print_json(n_out, &q_out);
    }
}