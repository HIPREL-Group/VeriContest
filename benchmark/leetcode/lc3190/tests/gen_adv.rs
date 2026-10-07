use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    len: usize,
    values: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= len <= 50,
        values.len() == len,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 50,
    ensures
        1 <= nums.len() <= 50,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 50,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            1 <= len <= 50,
            values.len() == len,
            nums.len() == i,
            forall|k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 50,
            forall|k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 50,
            forall|k: int| 0 <= k < nums.len() ==> #[trigger] nums[k] == values[k],
        decreases len - i,
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

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        let v = (self.next_u64() % span) as i32;
        lo + v
    }
}

fn build_values(rng: &mut Rng, mode: usize, len: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(len);
    match mode {
        0 => {
            // all divisible by 3
            for _ in 0..len {
                let k = rng.gen_range_i32(1, 16); // 1..=16 -> *3 -> 3..=48
                v.push(k * 3);
            }
        }
        1 => {
            // none divisible by 3
            for _ in 0..len {
                let mut x = rng.gen_range_i32(1, 50);
                if x % 3 == 0 {
                    if x == 3 { x = 1; } else { x = x - 1; }
                }
                v.push(x);
            }
        }
        2 => {
            // all 1s
            for _ in 0..len { v.push(1); }
        }
        3 => {
            // all 3s
            for _ in 0..len { v.push(3); }
        }
        4 => {
            // all 50s
            for _ in 0..len { v.push(50); }
        }
        5 => {
            // all 49s (49 % 3 = 1)
            for _ in 0..len { v.push(49); }
        }
        6 => {
            // alternating 1,2
            for i in 0..len {
                v.push(if i % 2 == 0 { 1 } else { 2 });
            }
        }
        7 => {
            // random 1..=50
            for _ in 0..len {
                v.push(rng.gen_range_i32(1, 50));
            }
        }
        8 => {
            // ascending
            for i in 0..len {
                v.push((i as i32 % 50) + 1);
            }
        }
        9 => {
            // boundary values
            for i in 0..len {
                let choices = [1i32, 2, 3, 49, 50];
                v.push(choices[i % 5]);
            }
        }
        _ => {
            for _ in 0..len {
                v.push(rng.gen_range_i32(1, 50));
            }
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
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let modes = 10usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let len = match mode {
            0 => 1 + (t % 50),
            1 => 1 + (t % 50),
            2 => 1,
            3 => 50,
            4 => 50,
            5 => 25,
            6 => 2 + (t % 49),
            7 => rng.gen_range_usize(1, 50),
            8 => 1 + (t % 50),
            _ => rng.gen_range_usize(1, 50),
        };
        let len = if len < 1 { 1 } else if len > 50 { 50 } else { len };
        let values = build_values(&mut rng, mode, len);
        let nums = generate_test_case(len, &values);
        print_json(&nums);
    }
}