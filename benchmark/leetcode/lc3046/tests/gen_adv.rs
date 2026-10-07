use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    len_half: usize,
    values: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= len_half <= 50,
        values.len() == 2 * len_half,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100,
    ensures
        1 <= nums.len() <= 100,
        nums.len() % 2 == 0,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
{
    let n: usize = 2 * len_half;
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == 2 * len_half,
            1 <= len_half <= 50,
            values.len() == n,
            0 <= i <= n,
            nums.len() == i,
            forall|k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 100,
            forall|k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 100,
        decreases n - i,
    {
        nums.push(values[i]);
        i = i + 1;
    }
    assert(nums.len() == n);
    assert(n % 2 == 0);
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
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
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

fn build_values(rng: &mut Rng, mode: usize, len_half: usize) -> Vec<i32> {
    let n = 2 * len_half;
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // all same value - should return false
            let x = rng.gen_range_i32(1, 100);
            for _ in 0..n { v.push(x); }
        }
        1 => {
            // each element appears exactly twice - should return true
            for i in 0..len_half {
                let x = ((i % 100) + 1) as i32;
                v.push(x);
                v.push(x);
            }
        }
        2 => {
            // all distinct - true
            for i in 0..n {
                v.push(((i % 100) + 1) as i32);
            }
        }
        3 => {
            // one element appears 3 times - should return false
            let x = rng.gen_range_i32(1, 100);
            v.push(x); v.push(x); v.push(x);
            let mut cur: i32 = 1;
            while v.len() < n {
                if cur != x {
                    v.push(cur);
                }
                cur = (cur % 100) + 1;
            }
        }
        4 => {
            // random values
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100));
            }
        }
        5 => {
            // two values alternating
            let a = rng.gen_range_i32(1, 50);
            let b = rng.gen_range_i32(51, 100);
            for i in 0..n {
                v.push(if i % 2 == 0 { a } else { b });
            }
        }
        6 => {
            // values restricted to small range
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 3));
            }
        }
        7 => {
            // one element exactly len_half+1 times - false
            let x = rng.gen_range_i32(1, 100);
            let count = len_half + 1;
            for _ in 0..count { v.push(x); }
            let mut cur: i32 = 1;
            while v.len() < n {
                if cur != x { v.push(cur); }
                cur = (cur % 100) + 1;
            }
        }
        8 => {
            // one element exactly len_half times, rest distinct - true
            let x = rng.gen_range_i32(1, 100);
            for _ in 0..len_half { v.push(x); }
            let mut cur: i32 = 1;
            while v.len() < n {
                if cur != x { v.push(cur); }
                cur = (cur % 100) + 1;
            }
        }
        9 => {
            // boundary: all values equal to 1 or 100
            for i in 0..n {
                v.push(if i % 2 == 0 { 1 } else { 100 });
            }
        }
        _ => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100));
            }
        }
    }
    while v.len() < n {
        v.push(1);
    }
    v.truncate(n);
    for x in v.iter_mut() {
        if *x < 1 { *x = 1; }
        if *x > 100 { *x = 100; }
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
        let len_half: usize = match mode {
            0 => 1 + (t % 50),
            1 => 1 + (t % 50),
            2 => 1 + (t % 50),
            3 => 2 + (t % 49),
            4 => 1 + (t % 50),
            5 => 1 + (t % 50),
            6 => 1 + (t % 50),
            7 => 2 + (t % 49),
            8 => 1 + (t % 50),
            9 => 1 + (t % 50),
            _ => 1 + (t % 50),
        };
        let len_half = if len_half < 1 { 1 } else if len_half > 50 { 50 } else { len_half };

        let values = build_values(&mut rng, mode, len_half);
        let nums = generate_test_case(len_half, &values);
        print_json(&nums);
    }
}