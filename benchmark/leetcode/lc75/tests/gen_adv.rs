use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 300,
        forall|i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 2,
    ensures
        1 <= nums.len() <= 300,
        nums.len() == values.len(),
        forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 2,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            nums.len() == i,
            forall|k: int| 0 <= k < i as int ==> 0 <= #[trigger] nums[k] <= 2,
            forall|k: int| 0 <= k < values.len() ==> 0 <= #[trigger] values[k] <= 2,
        decreases n - i,
    {
        let v = values[i];
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
}

fn make_values(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            for _ in 0..n { v.push(rng.gen_range_usize(0, 2) as i32); }
        }
        1 => {
            for _ in 0..n { v.push(0); }
        }
        2 => {
            for _ in 0..n { v.push(1); }
        }
        3 => {
            for _ in 0..n { v.push(2); }
        }
        4 => {
            // all 0 then all 2 (no 1)
            let half = n / 2;
            for i in 0..n {
                if i < half { v.push(0); } else { v.push(2); }
            }
        }
        5 => {
            // reverse sorted: 2,2,1,1,0,0
            let third = n / 3;
            for i in 0..n {
                if i < third { v.push(2); }
                else if i < 2*third { v.push(1); }
                else { v.push(0); }
            }
        }
        6 => {
            // already sorted
            let third = n / 3;
            for i in 0..n {
                if i < third { v.push(0); }
                else if i < 2*third { v.push(1); }
                else { v.push(2); }
            }
        }
        7 => {
            // alternating 0,2
            for i in 0..n {
                if i % 2 == 0 { v.push(0); } else { v.push(2); }
            }
        }
        8 => {
            // alternating 0,1,2
            for i in 0..n {
                v.push((i % 3) as i32);
            }
        }
        9 => {
            // mostly 1s with edges
            for i in 0..n {
                if i == 0 { v.push(2); }
                else if i == n-1 { v.push(0); }
                else { v.push(1); }
            }
        }
        _ => {
            for _ in 0..n { v.push(rng.gen_range_usize(0, 2) as i32); }
        }
    }
    v
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
    } else { 1 };

    let mut rng = Rng::new(seed);
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => rng.gen_range_usize(1, 300),
            1 => 1,
            2 => 2,
            3 => 300,
            4 => rng.gen_range_usize(2, 10),
            5 => 299,
            6 => rng.gen_range_usize(50, 150),
            7 => rng.gen_range_usize(1, 50),
            8 => rng.gen_range_usize(100, 300),
            9 => rng.gen_range_usize(3, 20),
            _ => rng.gen_range_usize(1, 300),
        };
        let n = if n < 1 { 1 } else if n > 300 { 300 } else { n };
        let values = make_values(&mut rng, mode, n);
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}