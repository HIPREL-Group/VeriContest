use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 100,
        forall |i: int| 0 <= i < values.len() ==> -100 <= #[trigger] values[i] <= 100,
    ensures
        1 <= nums.len() <= 100,
        forall |i: int| 0 <= i < nums.len() ==> -100 <= #[trigger] nums[i] <= 100,
{
    let mut nums: Vec<i32> = Vec::new();
    let n: usize = values.len();
    let mut pos: usize = 0;
    while pos < n
        invariant
            n == values.len(),
            1 <= n <= 100,
            0 <= pos <= n,
            nums.len() == pos,
            forall |i: int| 0 <= i < values.len() ==> -100 <= #[trigger] values[i] <= 100,
            forall |k: int| 0 <= k < pos as int ==> #[trigger] nums[k] == values[k],
            forall |k: int| 0 <= k < pos as int ==> -100 <= #[trigger] nums[k] <= 100,
        decreases n - pos,
    {
        let v = values[pos];
        nums.push(v);
        pos = pos + 1;
    }
    nums
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
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + ((self.next_u64() % span) as i32)
    }
}

fn build(mode: usize, rng: &mut Rng) -> Vec<i32> {
    match mode {
        0 => {
            // minimal length
            vec![rng.gen_range_i32(-100, 100)]
        }
        1 => {
            // all zeros
            let n = rng.gen_range_usize(1, 100);
            vec![0i32; n]
        }
        2 => {
            // all positive max
            let n = rng.gen_range_usize(1, 100);
            vec![100i32; n]
        }
        3 => {
            // all negative max
            let n = rng.gen_range_usize(1, 100);
            vec![-100i32; n]
        }
        4 => {
            // maximum length random
            let n = 100;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(-100, 100));
            }
            v
        }
        5 => {
            // small length, large positive values (causes many wraps)
            let n = rng.gen_range_usize(2, 5);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(50, 100));
            }
            v
        }
        6 => {
            // small length, large negative
            let n = rng.gen_range_usize(2, 5);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(-100, -50));
            }
            v
        }
        7 => {
            // mix of pos/neg/zero
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                let choice = rng.gen_range_usize(0, 2);
                match choice {
                    0 => v.push(0),
                    1 => v.push(rng.gen_range_i32(1, 100)),
                    _ => v.push(rng.gen_range_i32(-100, -1)),
                }
            }
            v
        }
        8 => {
            // length equal to value (tests exact wrap)
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::with_capacity(n);
            let val = n as i32;
            let val = if val > 100 { 100 } else { val };
            for _ in 0..n {
                v.push(val);
            }
            v
        }
        9 => {
            // length equal to value but negative
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::with_capacity(n);
            let val = -(n as i32);
            let val = if val < -100 { -100 } else { val };
            for _ in 0..n {
                v.push(val);
            }
            v
        }
        10 => {
            // examples
            vec![3, -2, 1, 1]
        }
        11 => {
            vec![-1, 4, -1]
        }
        _ => {
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(-100, 100));
            }
            v
        }
    }
}

fn print_json(nums: &[i32]) {
    print!("{{\"nums\":[");
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
    let modes = 12usize;
    let total = 220usize;

    for t in 0..total {
        let mode = if t < modes * 2 { t % modes } else { rng.gen_range_usize(0, modes + 3) };
        let values = build(mode, &mut rng);
        // clamp safety
        let mut clamped: Vec<i32> = Vec::with_capacity(values.len());
        for &x in &values {
            let v = if x > 100 { 100 } else if x < -100 { -100 } else { x };
            clamped.push(v);
        }
        if clamped.is_empty() {
            clamped.push(0);
        }
        if clamped.len() > 100 {
            clamped.truncate(100);
        }
        let nums = generate_test_case(&clamped);
        print_json(&nums);
    }
}