use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    vals: &Vec<i32>,
    target: i32,
) -> (nums: Vec<i32>)
    requires
        1 <= vals.len() <= 50,
        -50 <= target <= 50,
        forall|k: int| 0 <= k < vals.len() ==> -50 <= #[trigger] vals[k] <= 50,
    ensures
        1 <= nums.len() <= 50,
        -50 <= target <= 50,
        forall|k: int| 0 <= k < nums.len() ==> -50 <= #[trigger] nums[k] <= 50,
{
    let mut nums: Vec<i32> = Vec::new();
    let n = vals.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == vals.len(),
            0 <= i <= n,
            nums.len() == i,
            forall|k: int| 0 <= k < vals.len() ==> -50 <= #[trigger] vals[k] <= 50,
            forall|k: int| 0 <= k < i as int ==> -50 <= #[trigger] nums[k] <= 50,
            forall|k: int| 0 <= k < i as int ==> nums[k] == vals[k],
        decreases n - i,
    {
        let v = vals[i];
        assert(-50 <= v <= 50);
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
        Self { state: seed }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build_vals(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(-50, 50));
            }
        }
        1 => {
            for _ in 0..n {
                v.push(-50);
            }
        }
        2 => {
            for _ in 0..n {
                v.push(50);
            }
        }
        3 => {
            for _ in 0..n {
                v.push(0);
            }
        }
        4 => {
            for i in 0..n {
                v.push(if i % 2 == 0 { -50 } else { 50 });
            }
        }
        5 => {
            for i in 0..n {
                v.push(if i % 2 == 0 { -1 } else { 1 });
            }
        }
        6 => {
            for i in 0..n {
                let x = (i as i32) - 25;
                let c = if x < -50 { -50 } else if x > 50 { 50 } else { x };
                v.push(c);
            }
        }
        7 => {
            for i in 0..n {
                let x = 25 - (i as i32);
                let c = if x < -50 { -50 } else if x > 50 { 50 } else { x };
                v.push(c);
            }
        }
        8 => {
            let c = rng.gen_range_i32(-50, 50);
            for _ in 0..n {
                v.push(c);
            }
        }
        9 => {
            for _ in 0..n {
                let r = rng.gen_range_i32(0, 2);
                v.push(if r == 0 { -50 } else if r == 1 { 0 } else { 50 });
            }
        }
        _ => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(-5, 5));
            }
        }
    }
    v
}

fn pick_target(rng: &mut Rng, mode: usize) -> i32 {
    match mode {
        0 => rng.gen_range_i32(-50, 50),
        1 => -50,
        2 => 50,
        3 => 0,
        4 => 0,
        5 => 0,
        6 => rng.gen_range_i32(-10, 10),
        7 => rng.gen_range_i32(-10, 10),
        8 => rng.gen_range_i32(-50, 50),
        9 => rng.gen_range_i32(-50, 50),
        _ => rng.gen_range_i32(-5, 5),
    }
}

fn print_json(nums: &[i32], target: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", nums[i]);
    }
    println!("],\"target\":{}}}", target);
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
        let n = match mode {
            0 => 1 + (t % 50),
            1 => 50,
            2 => 50,
            3 => 1,
            4 => 2 + (t % 48),
            5 => 10,
            6 => 50,
            7 => 50,
            8 => 1 + (t % 50),
            9 => 20,
            _ => 1 + (t % 50),
        };
        let n = if n == 0 { 1 } else if n > 50 { 50 } else { n };

        let vals = build_vals(&mut rng, mode, n);
        let target = pick_target(&mut rng, mode);
        let nums = generate_test_case(&vals, target);
        print_json(&nums, target);
    }
}