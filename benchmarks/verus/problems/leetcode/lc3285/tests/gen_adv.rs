use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
    threshold: i32,
) -> (height: Vec<i32>)
    requires
        2 <= values.len() <= 100,
        1 <= threshold <= 100,
        forall|j: int| 0 <= j < values.len() ==> 1 <= #[trigger] values[j] <= 100,
    ensures
        2 <= height.len() <= 100,
        forall|j: int| 0 <= j < height.len() ==> #[trigger] height[j] >= 1,
        forall|j: int| 0 <= j < height.len() ==> #[trigger] height[j] <= 100,
        1 <= threshold <= 100,
{
    let n = values.len();
    let mut height: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            height.len() == i,
            forall|j: int| 0 <= j < i as int ==> #[trigger] height[j] == values[j],
            forall|j: int| 0 <= j < values.len() ==> 1 <= #[trigger] values[j] <= 100,
        decreases n - i,
    {
        height.push(values[i]);
        i += 1;
    }
    assert(forall|j: int| 0 <= j < height.len() ==> height[j] == values[j]);
    height
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn make_values(rng: &mut Rng, n: usize, mode: usize, threshold: i32) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    for i in 0..n {
        let x: i32 = match mode {
            0 => rng.gen_range_i32(1, 100),
            1 => 1,
            2 => 100,
            3 => threshold,
            4 => if threshold < 100 { threshold + 1 } else { 100 },
            5 => if threshold > 1 { threshold - 1 } else { 1 },
            6 => if i % 2 == 0 { 1 } else { 100 },
            7 => (i as i32 % 100) + 1,
            8 => if rng.next_u64() % 2 == 0 { threshold } else { if threshold < 100 { threshold + 1 } else { threshold } },
            9 => {
                let r = rng.next_u64() % 3;
                if r == 0 { 1 } else if r == 1 { threshold } else { 100 }
            }
            _ => rng.gen_range_i32(1, 100),
        };
        let xx = if x < 1 { 1 } else if x > 100 { 100 } else { x };
        v.push(xx);
    }
    v
}

fn print_json(height: &[i32], threshold: i32) {
    print!("{{\"height\":[");
    for i in 0..height.len() {
        if i > 0 { print!(","); }
        print!("{}", height[i]);
    }
    println!("],\"threshold\":{}}}", threshold);
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
            0 => rng.gen_range_usize(2, 100),
            1 => 2,
            2 => 100,
            3 => rng.gen_range_usize(2, 10),
            4 => rng.gen_range_usize(50, 100),
            5 => 3,
            6 => rng.gen_range_usize(2, 100),
            7 => rng.gen_range_usize(2, 100),
            8 => rng.gen_range_usize(2, 100),
            _ => rng.gen_range_usize(2, 100),
        };
        let threshold = match mode {
            1 => 1,
            2 => 100,
            3 => rng.gen_range_i32(1, 100),
            _ => rng.gen_range_i32(1, 100),
        };
        let values = make_values(&mut rng, n, mode, threshold);
        let height = generate_test_case(&values, threshold);
        print_json(&height, threshold);
    }
}