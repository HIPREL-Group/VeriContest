use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 50,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 50,
    ensures
        1 <= nums.len() <= 50,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 50,
{
    let mut nums: Vec<i32> = Vec::new();
    let n = values.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 50,
            forall |k: int| 0 <= k < i as int ==> nums[k] == values[k],
            forall |k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 50,
        decreases n - i,
    {
        nums.push(values[i]);
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
    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_mode(rng: &mut Rng, mode: usize) -> Vec<i32> {
    match mode {
        0 => {
            // Sequential prefix covers all
            let len = rng.gen_range_usize(1, 10);
            let start = rng.gen_i32(1, 50 - len as i32 + 1).max(1);
            let start = start.min(50 - (len as i32 - 1));
            let start = if start < 1 { 1 } else { start };
            let mut v = Vec::new();
            for i in 0..len {
                let x = start + i as i32;
                if x >= 1 && x <= 50 {
                    v.push(x);
                } else {
                    v.push(1);
                }
            }
            v
        }
        1 => {
            // Single element
            vec![rng.gen_i32(1, 50)]
        }
        2 => {
            // All same value
            let v_val = rng.gen_i32(1, 50);
            let n = rng.gen_range_usize(1, 50);
            (0..n).map(|_| v_val).collect()
        }
        3 => {
            // Sequential prefix [1,2,3] then random
            let mut v = vec![1, 2, 3];
            let extra = rng.gen_range_usize(0, 20);
            for _ in 0..extra {
                v.push(rng.gen_i32(1, 50));
            }
            if v.len() > 50 { v.truncate(50); }
            v
        }
        4 => {
            // Max length
            (0..50).map(|_| rng.gen_i32(1, 50)).collect()
        }
        5 => {
            // Sequential prefix full, sum would be small
            vec![1, 2, 3, 4, 5]
        }
        6 => {
            // Starts with large values 
            vec![50, 50, 50, 50]
        }
        7 => {
            // Sum equals a value in array
            vec![1, 2, 3, 6]
        }
        8 => {
            // Long sequential prefix
            let mut v = Vec::new();
            let start = 1;
            for i in 0..10 {
                v.push(start + i);
            }
            v
        }
        9 => {
            // Contains consecutive integers from sum
            vec![3, 4, 5, 1, 12, 14, 13]
        }
        _ => {
            let n = rng.gen_range_usize(1, 50);
            (0..n).map(|_| rng.gen_i32(1, 50)).collect()
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
    } else { 1 };
    let mut rng = Rng::new(seed);

    let total = 220usize;
    let modes = 11usize;

    for t in 0..total {
        let mode = t % modes;
        let mut v = build_mode(&mut rng, mode);
        if v.is_empty() {
            v.push(1);
        }
        if v.len() > 50 {
            v.truncate(50);
        }
        // Clamp values to [1,50]
        for x in v.iter_mut() {
            if *x < 1 { *x = 1; }
            if *x > 50 { *x = 50; }
        }
        let nums = generate_test_case(&v);
        print_json(&nums);
    }
}