use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (height: Vec<i32>)
    requires
        1 <= values.len() <= 20_000,
        forall |i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 100_000,
    ensures
        1 <= height.len() <= 20_000,
        forall |i: int| 0 <= i < height.len() ==> 0 <= #[trigger] height[i] <= 100_000,
{
    let n = values.len();
    let mut height: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    while idx < n
        invariant
            n == values.len(),
            1 <= n <= 20_000,
            0 <= idx <= n,
            height.len() == idx,
            forall |i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 100_000,
            forall |i: int| 0 <= i < idx as int ==> #[trigger] height[i] == values[i],
        decreases n - idx,
    {
        height.push(values[idx]);
        idx = idx + 1;
    }
    height
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
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
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

fn build_values(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            // single element
            vec![rng.gen_range_i32(0, 100_000)]
        }
        1 => {
            // two elements
            vec![rng.gen_range_i32(0, 100_000), rng.gen_range_i32(0, 100_000)]
        }
        2 => {
            // all zeros
            let n = rng.gen_range_usize(1, 100);
            vec![0i32; n]
        }
        3 => {
            // all max
            let n = rng.gen_range_usize(1, 100);
            vec![100_000i32; n]
        }
        4 => {
            // strictly increasing
            let n = rng.gen_range_usize(2, 500);
            let mut v = Vec::new();
            for i in 0..n { v.push(i as i32); }
            v
        }
        5 => {
            // strictly decreasing
            let n = rng.gen_range_usize(2, 500);
            let mut v = Vec::new();
            for i in 0..n { v.push((n - i) as i32); }
            v
        }
        6 => {
            // V shape - maximum water
            let n = rng.gen_range_usize(3, 500);
            let mut v = Vec::new();
            let h = 100_000i32;
            v.push(h);
            for _ in 1..(n-1) { v.push(0); }
            v.push(h);
            v
        }
        7 => {
            // random small values
            let n = rng.gen_range_usize(1, 500);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(0, 10)); }
            v
        }
        8 => {
            // max size
            let n = 20_000;
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(0, 100_000)); }
            v
        }
        9 => {
            // sawtooth
            let n = rng.gen_range_usize(2, 500);
            let mut v = Vec::new();
            for i in 0..n {
                v.push(if i % 2 == 0 { rng.gen_range_i32(0, 10) } else { rng.gen_range_i32(50, 100) });
            }
            v
        }
        10 => {
            // example 1
            vec![0,1,0,2,1,0,1,3,2,1,2,1]
        }
        11 => {
            // example 2
            vec![4,2,0,3,2,5]
        }
        _ => {
            // random
            let n = rng.gen_range_usize(1, 1000);
            let mut v = Vec::new();
            let maxv = if t % 3 == 0 { 100_000 } else if t % 3 == 1 { 1000 } else { 10 };
            for _ in 0..n { v.push(rng.gen_range_i32(0, maxv)); }
            v
        }
    }
}

fn print_json(height: &[i32]) {
    print!("{{\"height\":[");
    for i in 0..height.len() {
        if i > 0 { print!(","); }
        print!("{}", height[i]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 13usize;
    let total = 200usize;
    for t in 0..total {
        let mode = if t < modes { t } else { (rng.next_u64() as usize) % modes };
        let values = build_values(&mut rng, mode, t);
        let height = generate_test_case(&values);
        print_json(&height);
    }
}