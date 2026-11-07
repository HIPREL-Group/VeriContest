use vstd::prelude::*;

verus! {

pub fn generate_test_case(fillers: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= fillers.len() <= 1000,
        forall|i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 1000,
    ensures
        1 <= nums.len() <= 1000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
{
    let mut nums: Vec<i32> = Vec::new();
    let n = fillers.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == fillers.len(),
            0 <= i <= n,
            nums.len() == i,
            forall|k: int| 0 <= k < fillers.len() ==> 1 <= #[trigger] fillers[k] <= 1000,
            forall|k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 1000,
        decreases n - i,
    {
        nums.push(fillers[i]);
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
        lo + (self.next_u64() % span) as i32
    }
}

fn build_fillers(mode: usize, rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    match mode {
        0 => {
            // all divisible-by-6 (even + div3)
            for _ in 0..n {
                let k = rng.gen_range_i32(1, 166);
                v.push(k * 6);
            }
        }
        1 => {
            // no valid numbers (odd or not div 3)
            for _ in 0..n {
                let c = rng.gen_range_usize(0, 2);
                let x = match c {
                    0 => {
                        // odd
                        let k = rng.gen_range_i32(0, 499);
                        2 * k + 1
                    }
                    1 => {
                        // even but not div 3
                        let mut k = rng.gen_range_i32(1, 500) * 2;
                        if k % 3 == 0 { k += 2; }
                        if k > 1000 { k = 1000 - (k % 3); if k % 2 != 0 { k -= 1; } }
                        if k < 1 { k = 2; }
                        k
                    }
                    _ => {
                        // odd div by 3
                        let k = rng.gen_range_i32(0, 166);
                        let x = 2 * k * 3 + 3;
                        if x > 1000 { 3 } else { x }
                    }
                };
                let xx = if x < 1 { 1 } else if x > 1000 { 1000 } else { x };
                v.push(xx);
            }
        }
        2 => {
            // all 1000
            for _ in 0..n { v.push(1000); }
        }
        3 => {
            // all 1
            for _ in 0..n { v.push(1); }
        }
        4 => {
            // all 6
            for _ in 0..n { v.push(6); }
        }
        5 => {
            // random
            for _ in 0..n { v.push(rng.gen_range_i32(1, 1000)); }
        }
        6 => {
            // single huge 996 multiple
            for _ in 0..n { v.push(996); }
        }
        7 => {
            // mix with one valid
            for _ in 0..n { v.push(rng.gen_range_i32(1, 1000)); }
            if n > 0 { v[0] = 6; }
        }
        8 => {
            // all 3 (odd, div3)
            for _ in 0..n { v.push(3); }
        }
        9 => {
            // all 2 (even, not div3)
            for _ in 0..n { v.push(2); }
        }
        _ => {
            for _ in 0..n { v.push(rng.gen_range_i32(1, 1000)); }
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
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => 1 + (t % 5),
            1 => 1000,
            2 => 17,
            3 => if t % 2 == 0 { 1 } else { 500 },
            4 => 3 + (t % 10),
            5 => rng.gen_range_usize(1, 1000),
            6 => 1000,
            7 => 50 + (t % 100),
            8 => 1,
            9 => 25,
            _ => 100,
        };
        let n = if n < 1 { 1 } else if n > 1000 { 1000 } else { n };

        let fillers = build_fillers(mode, &mut rng, n);
        let nums = generate_test_case(&fillers);
        print_json(&nums);
    }
}