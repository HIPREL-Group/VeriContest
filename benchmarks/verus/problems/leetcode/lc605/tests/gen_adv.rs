use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    pattern: &Vec<i32>,
    n_val: i32,
) -> (res: (Vec<i32>, i32))
    requires
        1 <= pattern.len() <= 20_000,
        forall |i: int| 0 <= i < pattern.len() ==> (#[trigger] pattern[i] == 0 || pattern[i] == 1),
        forall |i: int| 0 <= i < pattern.len() - 1 ==> !(#[trigger] pattern[i] == 1 && pattern[i + 1] == 1),
        0 <= n_val,
        n_val as int <= pattern.len() as int,
    ensures
        1 <= res.0.len() <= 20_000,
        forall |i: int| 0 <= i < res.0.len() ==> (#[trigger] res.0[i] == 0 || res.0[i] == 1),
        forall |i: int| 0 <= i < res.0.len() - 1 ==> !(#[trigger] res.0[i] == 1 && res.0[i + 1] == 1),
        0 <= res.1,
        res.1 as int <= res.0.len() as int,
{
    let mut out: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < pattern.len()
        invariant
            0 <= i <= pattern.len(),
            out.len() == i,
            forall |k: int| 0 <= k < i as int ==> out[k] == pattern[k],
        decreases pattern.len() - i,
    {
        out.push(pattern[i]);
        i = i + 1;
    }
    assert(out.len() == pattern.len());
    assert(forall |k: int| 0 <= k < out.len() ==> out[k] == pattern[k]);
    (out, n_val)
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

fn build_pattern_random(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(len);
    let mut prev = 0i32;
    for _ in 0..len {
        let r = rng.next_u64() % 2;
        let bit = if prev == 1 { 0i32 } else { r as i32 };
        v.push(bit);
        prev = bit;
    }
    v
}

fn build_all_zeros(len: usize) -> Vec<i32> {
    vec![0i32; len]
}

fn build_alternating_start_one(len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for i in 0..len {
        v.push(if i % 2 == 0 { 1 } else { 0 });
    }
    v
}

fn build_alternating_start_zero(len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for i in 0..len {
        v.push(if i % 2 == 1 { 1 } else { 0 });
    }
    v
}

fn build_single_one_middle(len: usize) -> Vec<i32> {
    let mut v = vec![0i32; len];
    if len > 0 {
        v[len / 2] = 1;
    }
    v
}

fn build_ones_at_ends(len: usize) -> Vec<i32> {
    let mut v = vec![0i32; len];
    if len >= 1 {
        v[0] = 1;
    }
    if len >= 3 {
        v[len - 1] = 1;
    }
    v
}

fn build_sparse_ones(len: usize, gap: usize) -> Vec<i32> {
    let mut v = vec![0i32; len];
    let g = if gap < 2 { 2 } else { gap };
    let mut i = 0;
    while i < len {
        v[i] = 1;
        i += g;
    }
    v
}

fn compute_max_additional(flowerbed: &Vec<i32>) -> i32 {
    let mut fb = flowerbed.clone();
    let mut count = 0i32;
    let n = fb.len();
    for i in 0..n {
        if fb[i] == 0 {
            let prev_empty = i == 0 || fb[i - 1] == 0;
            let next_empty = i + 1 == n || fb[i + 1] == 0;
            if prev_empty && next_empty {
                fb[i] = 1;
                count += 1;
            }
        }
    }
    count
}

fn print_json(flowerbed: &[i32], n: i32) {
    print!("{{\"flowerbed\":[");
    for i in 0..flowerbed.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", flowerbed[i]);
    }
    println!("],\"n\":{}}}", n);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let total = 220usize;

    for t in 0..total {
        let mode = t % 11;
        let len: usize = match mode {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => rng.gen_range_usize(1, 20),
            4 => rng.gen_range_usize(20, 200),
            5 => rng.gen_range_usize(200, 2000),
            6 => 20_000,
            7 => rng.gen_range_usize(1, 100),
            8 => rng.gen_range_usize(1, 100),
            9 => rng.gen_range_usize(1, 50),
            _ => rng.gen_range_usize(1, 500),
        };

        let pattern: Vec<i32> = match mode {
            0 => build_all_zeros(len),
            1 => build_all_zeros(len),
            2 => build_alternating_start_one(len),
            3 => build_random_valid(&mut rng, len),
            4 => build_alternating_start_zero(len),
            5 => build_random_valid(&mut rng, len),
            6 => build_all_zeros(len),
            7 => build_single_one_middle(len),
            8 => build_ones_at_ends(len),
            9 => build_sparse_ones(len, 3),
            _ => build_random_valid(&mut rng, len),
        };

        // Choose n. Sometimes at boundary (equal to max), sometimes 0, sometimes larger.
        let max_plant = compute_max_additional(&pattern);
        let nsel = rng.next_u64() % 5;
        let n_val: i32 = match nsel {
            0 => 0,
            1 => if max_plant > 0 { max_plant } else { 0 },
            2 => max_plant + 1,
            3 => {
                let upper = pattern.len() as i32;
                if upper == 0 { 0 } else { (rng.next_u64() as i32).rem_euclid(upper + 1) }
            }
            _ => {
                if max_plant > 0 {
                    (rng.next_u64() as i32).rem_euclid(max_plant + 2)
                } else {
                    0
                }
            }
        };

        let n_clamped = if n_val < 0 { 0 } else if (n_val as usize) > pattern.len() { pattern.len() as i32 } else { n_val };

        let (fb, nn) = generate_test_case(&pattern, n_clamped);
        print_json(&fb, nn);
    }
}

fn build_random_valid(rng: &mut Rng, len: usize) -> Vec<i32> {
    build_pattern_random(rng, len)
}