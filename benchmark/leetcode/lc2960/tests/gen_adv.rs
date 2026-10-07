use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (result: Vec<i32>)
    requires
        1 <= values.len() <= 100,
        forall|i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 100,
    ensures
        1 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 100,
{
    let n = values.len();
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            result.len() == i,
            forall|k: int| 0 <= k < values.len() ==> 0 <= #[trigger] values[k] <= 100,
            forall|k: int| 0 <= k < i as int ==> 0 <= #[trigger] result[k] <= 100,
        decreases n - i,
    {
        result.push(values[i]);
        i = i + 1;
    }
    result
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
        let span = (hi - lo + 1) as u32;
        lo + (self.next_u64() as u32 % span) as i32
    }
}

fn build(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            // random
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 100));
            }
            v
        }
        1 => {
            // all zeros
            let n = rng.gen_range_usize(1, 100);
            vec![0i32; n]
        }
        2 => {
            // all ones
            let n = rng.gen_range_usize(1, 100);
            vec![1i32; n]
        }
        3 => {
            // all 100
            let n = rng.gen_range_usize(1, 100);
            vec![100i32; n]
        }
        4 => {
            // single element
            vec![rng.gen_range_i32(0, 100)]
        }
        5 => {
            // alternating 0 and nonzero
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(0);
                } else {
                    v.push(rng.gen_range_i32(1, 100));
                }
            }
            v
        }
        6 => {
            // increasing
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for i in 0..n {
                v.push((i as i32).min(100));
            }
            v
        }
        7 => {
            // decreasing
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for i in 0..n {
                v.push(((n - 1 - i) as i32).min(100));
            }
            v
        }
        8 => {
            // small values 0-2
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 2));
            }
            v
        }
        9 => {
            // first element large rest varies
            let n = rng.gen_range_usize(2, 100);
            let mut v = vec![100i32];
            for _ in 1..n {
                v.push(rng.gen_range_i32(0, 5));
            }
            v
        }
        _ => {
            // max length
            let mut v = Vec::new();
            for _ in 0..100 {
                v.push(rng.gen_range_i32(0, 100));
            }
            let _ = t;
            v
        }
    }
}

fn print_json(nums: &[i32]) {
    print!("{{\"battery_percentages\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
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
    let total = 220usize;
    for t in 0..total {
        let mode = t % modes;
        let values = build(&mut rng, mode, t);
        let result = generate_test_case(&values);
        print_json(&result);
    }
}