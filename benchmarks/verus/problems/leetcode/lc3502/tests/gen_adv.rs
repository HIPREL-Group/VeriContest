use vstd::prelude::*;

verus! {

pub fn generate_test_case(cost: Vec<i32>) -> (out: Vec<i32>)
    requires
        1 <= cost.len() <= 100,
        forall |i: int| 0 <= i < cost.len() ==> 1 <= #[trigger] cost[i] <= 100,
    ensures
        1 <= out.len() <= 100,
        forall |i: int| 0 <= i < out.len() ==> 1 <= #[trigger] out[i] <= 100,
{
    cost
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

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_valid(v: Vec<i32>) -> Vec<i32> {
    // Clamp to [1, 100]
    let mut out = Vec::with_capacity(v.len());
    for x in v {
        let c = if x < 1 { 1 } else if x > 100 { 100 } else { x };
        out.push(c);
    }
    out
}

fn gen_mode(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            // Small random
            let n = 1 + (t % 10);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100));
            }
            v
        }
        1 => {
            // Single element
            vec![rng.gen_range_i32(1, 100)]
        }
        2 => {
            // Max size random
            let n = 100;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100));
            }
            v
        }
        3 => {
            // All same value
            let n = 1 + (t % 100);
            let x = rng.gen_range_i32(1, 100);
            vec![x; n]
        }
        4 => {
            // Strictly increasing
            let n = 1 + (t % 100);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push(((i % 100) + 1) as i32);
            }
            v
        }
        5 => {
            // Strictly decreasing
            let n = 1 + (t % 100);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                let x = 100 - (i as i32 % 100);
                v.push(if x < 1 { 1 } else { x });
            }
            v
        }
        6 => {
            // Minimum at index 0
            let n = 2 + (t % 99);
            let mut v = Vec::with_capacity(n);
            v.push(1);
            for _ in 1..n {
                v.push(rng.gen_range_i32(2, 100));
            }
            v
        }
        7 => {
            // Minimum at last index
            let n = 2 + (t % 99);
            let mut v = Vec::with_capacity(n);
            for _ in 0..(n - 1) {
                v.push(rng.gen_range_i32(2, 100));
            }
            v.push(1);
            v
        }
        8 => {
            // Minimum in the middle
            let n = 3 + (t % 97);
            let mid = n / 2;
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                if i == mid {
                    v.push(1);
                } else {
                    v.push(rng.gen_range_i32(2, 100));
                }
            }
            v
        }
        9 => {
            // All maxed out
            let n = 1 + (t % 100);
            vec![100; n]
        }
        _ => {
            // All minimum
            let n = 1 + (t % 100);
            vec![1; n]
        }
    }
}

fn print_json(cost: &[i32]) {
    print!("{{\"cost\":[");
    for i in 0..cost.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", cost[i]);
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
    let modes = 11usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let raw = gen_mode(&mut rng, mode, t);
        let clamped = build_valid(raw);
        // Ensure non-empty and <= 100
        let cost = if clamped.is_empty() {
            vec![1]
        } else if clamped.len() > 100 {
            clamped.into_iter().take(100).collect()
        } else {
            clamped
        };
        let out = generate_test_case(cost);
        print_json(&out);
    }
}