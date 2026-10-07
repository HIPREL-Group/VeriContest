use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 100,
        forall|i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 400,
    ensures
        1 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 400,
{
    let mut nums: Vec<i32> = Vec::new();
    let n = values.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            1 <= n <= 100,
            0 <= i <= n,
            nums.len() == i,
            forall|k: int| 0 <= k < values.len() ==> 0 <= #[trigger] values[k] <= 400,
            forall|k: int| 0 <= k < i as int ==> 0 <= #[trigger] nums[k] <= 400,
        decreases n - i,
    {
        let v = values[i];
        assert(0 <= v <= 400);
        nums.push(v);
        i = i + 1;
    }
    nums
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

fn build_values(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            // Length 1
            let v = rng.gen_range_i32(0, 400);
            vec![v]
        }
        1 => {
            // All zeros
            let n = rng.gen_range_usize(1, 100);
            vec![0i32; n]
        }
        2 => {
            // All max (400)
            let n = rng.gen_range_usize(1, 100);
            vec![400i32; n]
        }
        3 => {
            // Max length 100
            let mut v = Vec::new();
            for _ in 0..100 {
                v.push(rng.gen_range_i32(0, 400));
            }
            v
        }
        4 => {
            // Alternating high-low
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::new();
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(400);
                } else {
                    v.push(0);
                }
            }
            v
        }
        5 => {
            // Increasing
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::new();
            for i in 0..n {
                v.push((i as i32 * 4).min(400));
            }
            v
        }
        6 => {
            // Decreasing
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::new();
            for i in 0..n {
                let x = 400 - (i as i32 * 4);
                v.push(if x < 0 { 0 } else { x });
            }
            v
        }
        7 => {
            // Single spike in middle
            let n = rng.gen_range_usize(3, 100);
            let mut v = vec![0i32; n];
            v[n / 2] = 400;
            v
        }
        8 => {
            // Two length (adjacent choice)
            let a = rng.gen_range_i32(0, 400);
            let b = rng.gen_range_i32(0, 400);
            vec![a, b]
        }
        9 => {
            // Three length tricky
            let a = rng.gen_range_i32(0, 400);
            let b = rng.gen_range_i32(0, 400);
            let c = rng.gen_range_i32(0, 400);
            vec![a, b, c]
        }
        10 => {
            // Many small values
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 5));
            }
            v
        }
        11 => {
            // Pattern like 2,1,1,2
            let n = rng.gen_range_usize(4, 100);
            let mut v = Vec::new();
            for i in 0..n {
                if i == 0 || i == n - 1 {
                    v.push(2);
                } else {
                    v.push(1);
                }
            }
            v
        }
        _ => {
            // Random
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 400));
            }
            v
            // unused t
            // let _ = t;
        }
    }
}

fn print_json(nums: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 {
            print!(",");
        }
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
    let modes = 13usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let values = build_values(&mut rng, mode, t);
        // Safety: ensure non-empty and size <= 100
        let values = if values.is_empty() {
            vec![0i32]
        } else if values.len() > 100 {
            values[..100].to_vec()
        } else {
            values
        };
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}