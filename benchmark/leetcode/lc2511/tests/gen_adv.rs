use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (forts: Vec<i32>)
    requires
        1 <= values.len() <= 1000,
        forall|i: int| 0 <= i < values.len() ==>
            (#[trigger] values[i] == -1 || values[i] == 0 || values[i] == 1),
    ensures
        1 <= forts.len() <= 1000,
        forall|i: int| 0 <= i < forts.len() ==>
            (#[trigger] forts[i] == -1 || forts[i] == 0 || forts[i] == 1),
{
    let mut forts: Vec<i32> = Vec::new();
    let n = values.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            forts.len() == i,
            forall|k: int| 0 <= k < i as int ==>
                (#[trigger] forts[k] == values[k]),
            forall|k: int| 0 <= k < values.len() ==>
                (#[trigger] values[k] == -1 || values[k] == 0 || values[k] == 1),
        decreases n - i,
    {
        forts.push(values[i]);
        i = i + 1;
    }
    forts
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
    fn pick_val(&mut self) -> i32 {
        let r = self.next_u64() % 3;
        match r {
            0 => -1,
            1 => 0,
            _ => 1,
        }
    }
}

fn gen_random(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.pick_val());
    }
    v
}

fn gen_all_zero(n: usize) -> Vec<i32> {
    vec![0i32; n]
}

fn gen_all_ones(n: usize) -> Vec<i32> {
    vec![1i32; n]
}

fn gen_all_neg(n: usize) -> Vec<i32> {
    vec![-1i32; n]
}

fn gen_one_then_zeros_then_neg(n: usize) -> Vec<i32> {
    if n < 2 { return vec![1i32; n]; }
    let mut v = Vec::with_capacity(n);
    v.push(1);
    for _ in 1..(n-1) { v.push(0); }
    v.push(-1);
    v
}

fn gen_neg_then_zeros_then_one(n: usize) -> Vec<i32> {
    if n < 2 { return vec![-1i32; n]; }
    let mut v = Vec::with_capacity(n);
    v.push(-1);
    for _ in 1..(n-1) { v.push(0); }
    v.push(1);
    v
}

fn gen_alt_ones_negs(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        if i % 2 == 0 { v.push(1); } else { v.push(-1); }
    }
    v
}

fn gen_alt_one_zero(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        if i % 2 == 0 { v.push(1); } else { v.push(0); }
    }
    v
}

fn gen_blocks_zero_between(rng: &mut Rng, n: usize) -> Vec<i32> {
    // Random pattern of 1, -1 separated by blocks of zeros
    let mut v = Vec::with_capacity(n);
    let mut i = 0;
    while i < n {
        let marker = rng.next_u64() % 2;
        if marker == 0 { v.push(1); } else { v.push(-1); }
        i += 1;
        let gap = (rng.next_u64() as usize) % 10;
        let mut g = 0;
        while g < gap && i < n {
            v.push(0);
            i += 1;
            g += 1;
        }
    }
    v
}

fn gen_sparse_markers(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = vec![0i32; n];
    let count = rng.gen_range_usize(1, (n/20).max(1));
    for _ in 0..count {
        let idx = rng.gen_range_usize(0, n-1);
        v[idx] = if rng.next_u64() % 2 == 0 { 1 } else { -1 };
    }
    v
}

fn print_json(forts: &[i32]) {
    print!("{{\"forts\":[");
    for i in 0..forts.len() {
        if i > 0 { print!(","); }
        print!("{}", forts[i]);
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
    let modes = 10usize;

    for t in 0..total {
        let mode = t % modes;
        let n: usize = match mode {
            0 => 1,
            1 => 2,
            2 => 1000,
            3 => rng.gen_range_usize(1, 20),
            4 => rng.gen_range_usize(50, 200),
            5 => rng.gen_range_usize(500, 1000),
            6 => rng.gen_range_usize(1, 1000),
            7 => 1000,
            8 => rng.gen_range_usize(3, 50),
            _ => rng.gen_range_usize(1, 1000),
        };

        let values: Vec<i32> = match mode {
            0 => gen_random(&mut rng, n),
            1 => gen_alt_ones_negs(n),
            2 => gen_blocks_zero_between(&mut rng, n),
            3 => gen_one_then_zeros_then_neg(n),
            4 => gen_neg_then_zeros_then_one(n),
            5 => gen_sparse_markers(&mut rng, n),
            6 => {
                let r = rng.next_u64() % 3;
                match r {
                    0 => gen_all_zero(n),
                    1 => gen_all_ones(n),
                    _ => gen_all_neg(n),
                }
            }
            7 => gen_alt_one_zero(n),
            8 => gen_random(&mut rng, n),
            _ => gen_blocks_zero_between(&mut rng, n),
        };

        let forts = generate_test_case(&values);
        print_json(&forts);
    }
}