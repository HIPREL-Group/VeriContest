use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    vals1: &Vec<i32>,
    vals2: &Vec<i32>,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= vals1.len() <= 1000,
        1 <= vals2.len() <= 1000,
        forall |i: int| 0 <= i < vals1.len() ==> 1 <= #[trigger] vals1[i] <= 100_000,
        forall |i: int| 0 <= i < vals2.len() ==> 1 <= #[trigger] vals2[i] <= 100_000,
    ensures
        1 <= result.0.len() <= 1000,
        1 <= result.1.len() <= 1000,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100_000,
        forall |i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 100_000,
{
    let mut n1: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < vals1.len()
        invariant
            0 <= i <= vals1.len(),
            n1.len() == i,
            forall |k: int| 0 <= k < vals1.len() ==> 1 <= #[trigger] vals1[k] <= 100_000,
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] n1[k] <= 100_000,
        decreases vals1.len() - i,
    {
        n1.push(vals1[i]);
        i = i + 1;
    }

    let mut n2: Vec<i32> = Vec::new();
    let mut j: usize = 0;
    while j < vals2.len()
        invariant
            0 <= j <= vals2.len(),
            n2.len() == j,
            forall |k: int| 0 <= k < vals2.len() ==> 1 <= #[trigger] vals2[k] <= 100_000,
            forall |k: int| 0 <= k < j as int ==> 1 <= #[trigger] n2[k] <= 100_000,
        decreases vals2.len() - j,
    {
        n2.push(vals2[j]);
        j = j + 1;
    }

    (n1, n2)
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
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn make_random(rng: &mut Rng, n: usize, lo: i32, hi: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i32(lo, hi));
    }
    v
}

fn make_all_ones(n: usize) -> Vec<i32> {
    vec![1i32; n]
}

fn make_all_same(n: usize, x: i32) -> Vec<i32> {
    vec![x; n]
}

fn make_small(rng: &mut Rng, n: usize) -> Vec<i32> {
    make_random(rng, n, 1, 10)
}

fn make_with_squares(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    let bases = [2i32, 3, 4, 5, 6, 7, 8, 9, 10, 12];
    for _ in 0..n {
        let b = bases[(rng.next_u64() as usize) % bases.len()];
        if rng.next_u64() % 2 == 0 {
            v.push(b);
        } else {
            v.push(b * b);
        }
    }
    v
}

fn make_powers_of_two(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    let powers = [1i32, 2, 4, 8, 16, 32, 64, 128, 256];
    for _ in 0..n {
        v.push(powers[(rng.next_u64() as usize) % powers.len()]);
    }
    v
}

fn make_max_values(rng: &mut Rng, n: usize) -> Vec<i32> {
    make_random(rng, n, 99_000, 100_000)
}

fn make_large_squares(rng: &mut Rng, n: usize) -> Vec<i32> {
    // Values whose squares approach overflow; factor-pair triplets
    let mut v = Vec::with_capacity(n);
    let pool = [100i32, 200, 316, 1000, 316, 100_000];
    for _ in 0..n {
        v.push(pool[(rng.next_u64() as usize) % pool.len()]);
    }
    v
}

fn print_json(n1: &[i32], n2: &[i32]) {
    print!("{{\"nums1\":[");
    for i in 0..n1.len() {
        if i > 0 { print!(","); }
        print!("{}", n1[i]);
    }
    print!("],\"nums2\":[");
    for i in 0..n2.len() {
        if i > 0 { print!(","); }
        print!("{}", n2[i]);
    }
    println!("]}}");
}

fn gen_for_mode(rng: &mut Rng, mode: usize, t: usize) -> (Vec<i32>, Vec<i32>) {
    match mode {
        0 => {
            let n1 = 1 + (t % 5);
            let n2 = 1 + ((t + 1) % 5);
            (make_small(rng, n1), make_small(rng, n2))
        }
        1 => {
            let n1 = 1 + (t % 10);
            let n2 = 1 + (t % 10);
            (make_all_ones(n1), make_all_ones(n2))
        }
        2 => {
            (make_all_same(1000, 1), make_all_same(1000, 1))
        }
        3 => {
            let n1 = 100 + (t % 50);
            let n2 = 100 + (t % 50);
            (make_with_squares(rng, n1), make_with_squares(rng, n2))
        }
        4 => {
            let n1 = 200 + (t % 100);
            let n2 = 200 + (t % 100);
            (make_powers_of_two(rng, n1), make_powers_of_two(rng, n2))
        }
        5 => {
            let n1 = 500 + (t % 500);
            let n2 = 500 + (t % 500);
            (make_max_values(rng, n1), make_max_values(rng, n2))
        }
        6 => {
            (make_large_squares(rng, 1000), make_large_squares(rng, 1000))
        }
        7 => {
            // One small one large
            let n1 = 1;
            let n2 = 1000;
            (make_small(rng, n1), make_small(rng, n2))
        }
        8 => {
            // Specifically build a triplet case: nums1 contains x, nums2 contains a,b with a*b==x*x
            let mut n1 = vec![4i32, 7, 12];
            let mut n2 = vec![2i32, 8, 3, 16];
            for _ in 0..20 {
                n1.push(rng.gen_range_i32(1, 100));
                n2.push(rng.gen_range_i32(1, 100));
            }
            (n1, n2)
        }
        9 => {
            // Max size, moderate random values
            let vals = make_random(rng, 1000, 1, 1000);
            let vals2 = make_random(rng, 1000, 1, 1000);
            (vals, vals2)
        }
        _ => {
            let n1 = rng.gen_range_usize(1, 1000);
            let n2 = rng.gen_range_usize(1, 1000);
            (make_random(rng, n1, 1, 100_000), make_random(rng, n2, 1, 100_000))
        }
    }
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
        let (v1, v2) = gen_for_mode(&mut rng, mode, t);
        // Sanity clamp - ensure all in [1, 100_000] and length in [1, 1000]
        let mut s1: Vec<i32> = v1.into_iter().map(|x| {
            if x < 1 { 1 } else if x > 100_000 { 100_000 } else { x }
        }).collect();
        let mut s2: Vec<i32> = v2.into_iter().map(|x| {
            if x < 1 { 1 } else if x > 100_000 { 100_000 } else { x }
        }).collect();
        if s1.is_empty() { s1.push(1); }
        if s2.is_empty() { s2.push(1); }
        if s1.len() > 1000 { s1.truncate(1000); }
        if s2.len() > 1000 { s2.truncate(1000); }

        let (n1, n2) = generate_test_case(&s1, &s2);
        print_json(&n1, &n2);
    }
}