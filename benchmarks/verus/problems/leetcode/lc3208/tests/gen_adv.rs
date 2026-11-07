use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    pattern: &Vec<i32>,
    k: i32,
) -> (result: (Vec<i32>, i32))
    requires
        3 <= pattern.len() <= 100000,
        3 <= k <= pattern.len(),
        forall |i: int| 0 <= i < pattern.len() ==> (#[trigger] pattern[i] == 0 || pattern[i] == 1),
    ensures
        3 <= result.0.len() <= 100000,
        3 <= result.1 <= result.0.len(),
        forall |i: int| 0 <= i < result.0.len() ==> (#[trigger] result.0[i] == 0 || result.0[i] == 1),
{
    let mut colors: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    let n = pattern.len();

    while idx < n
        invariant
            n == pattern.len(),
            3 <= n <= 100000,
            0 <= idx <= n,
            colors.len() == idx,
            forall |i: int| 0 <= i < idx as int ==> (#[trigger] colors[i] == pattern[i]),
            forall |i: int| 0 <= i < pattern.len() ==> (#[trigger] pattern[i] == 0 || pattern[i] == 1),
        decreases n - idx,
    {
        colors.push(pattern[idx]);
        idx = idx + 1;
    }

    assert(colors.len() == n);
    assert forall |i: int| 0 <= i < colors.len() implies (#[trigger] colors[i] == 0 || colors[i] == 1) by {
        assert(colors[i] == pattern[i]);
    }

    (colors, k)
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
}

fn build_pattern(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    match mode {
        0 => {
            // Fully alternating
            for i in 0..n {
                v.push((i % 2) as i32);
            }
        }
        1 => {
            // All zeros
            for _ in 0..n {
                v.push(0);
            }
        }
        2 => {
            // All ones
            for _ in 0..n {
                v.push(1);
            }
        }
        3 => {
            // Alternating starting with 1
            for i in 0..n {
                v.push(((i + 1) % 2) as i32);
            }
        }
        4 => {
            // One block of non-alternating
            for i in 0..n {
                v.push((i % 2) as i32);
            }
            if n >= 2 {
                v[1] = 0;
            }
        }
        5 => {
            // Half zeros, half ones
            for i in 0..n {
                v.push(if i < n / 2 { 0 } else { 1 });
            }
        }
        6 => {
            // Random
            for _ in 0..n {
                v.push((rng.next_u64() % 2) as i32);
            }
        }
        7 => {
            // Mostly alternating, one flip
            for i in 0..n {
                v.push((i % 2) as i32);
            }
            let idx = rng.gen_range_usize(0, n - 1);
            v[idx] = 1 - v[idx];
        }
        8 => {
            // Runs of length 2
            for i in 0..n {
                v.push(((i / 2) % 2) as i32);
            }
        }
        9 => {
            // Alternating except last element breaks circular
            for i in 0..n {
                v.push((i % 2) as i32);
            }
            if n % 2 == 0 {
                // naturally breaks; do nothing
            } else {
                v[n - 1] = v[0];
            }
        }
        _ => {
            for _ in 0..n {
                v.push((rng.next_u64() % 2) as i32);
            }
        }
    }
    v
}

fn print_json(colors: &[i32], k: i32) {
    print!("{{\"colors\":[");
    for i in 0..colors.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", colors[i]);
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
        // Choose n
        let n: usize = match t % 7 {
            0 => 3,
            1 => 4,
            2 => 5,
            3 => 10,
            4 => 50 + (t % 50),
            5 => 1000 + (t % 100),
            _ => {
                let r = rng.gen_range_usize(3, 500);
                r
            }
        };

        // k in [3, n]
        let k: i32 = if n == 3 {
            3
        } else {
            let kk = match t % 5 {
                0 => 3,
                1 => n as i32,
                2 => ((n / 2) as i32).max(3),
                3 => ((n - 1) as i32).max(3),
                _ => rng.gen_range_usize(3, n) as i32,
            };
            kk
        };

        let pattern = build_pattern(&mut rng, mode, n);
        let (colors, k_out) = generate_test_case(&pattern, k);
        print_json(&colors, k_out);
    }
}