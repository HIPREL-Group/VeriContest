use vstd::prelude::*;

verus! {

pub fn generate_test_case(vals: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= vals.len() <= 100,
        forall |i: int| 0 <= i < vals.len() ==> vals[i] == -1i32 || (1 <= #[trigger] vals[i] <= 100),
    ensures
        1 <= nums.len() <= 100,
        forall |i: int| 0 <= i < nums.len() ==> nums[i] == -1i32 || (1 <= #[trigger] nums[i] <= 100),
        nums@ == vals@,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut pos: usize = 0;
    let n: usize = vals.len();

    while pos < n
        invariant
            n == vals.len(),
            0 <= pos <= n,
            nums.len() == pos,
            forall |i: int| 0 <= i < pos as int ==> #[trigger] nums[i] == vals[i],
            forall |i: int| 0 <= i < vals.len() ==> vals[i] == -1i32 || (1 <= #[trigger] vals[i] <= 100),
        decreases n - pos,
    {
        nums.push(vals[pos]);
        pos = pos + 1;
    }

    assert(nums@ =~= vals@);
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
    fn gen_elem(&mut self, p_minus_one: u32) -> i32 {
        // p_minus_one is 0..100 probability percent
        let r = self.gen_range_usize(0, 99) as u32;
        if r < p_minus_one {
            -1i32
        } else {
            self.gen_range_i32(1, 100)
        }
    }
}

fn build(n: usize, rng: &mut Rng, p: u32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_elem(p));
    }
    v
}

fn adversarial(mode: usize, rng: &mut Rng) -> Vec<i32> {
    match mode {
        0 => {
            // All -1
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n { v.push(-1i32); }
            v
        }
        1 => {
            // All positives
            let n = rng.gen_range_usize(1, 100);
            build(n, rng, 0)
        }
        2 => {
            // Single element -1
            vec![-1i32]
        }
        3 => {
            // Single positive
            vec![rng.gen_range_i32(1, 100)]
        }
        4 => {
            // Alternating positive and -1
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(rng.gen_range_i32(1, 100));
                } else {
                    v.push(-1i32);
                }
            }
            v
        }
        5 => {
            // Many -1s at end
            let n = 100;
            let mut v = Vec::with_capacity(n);
            v.push(rng.gen_range_i32(1, 100));
            v.push(rng.gen_range_i32(1, 100));
            for _ in 2..n { v.push(-1i32); }
            v
        }
        6 => {
            // Many -1s at start then positives (all -1 get -1)
            let n = 50;
            let mut v = Vec::with_capacity(n);
            for _ in 0..25 { v.push(-1i32); }
            for _ in 25..n { v.push(rng.gen_range_i32(1, 100)); }
            v
        }
        7 => {
            // Example 1
            vec![1, 2, -1, -1, -1]
        }
        8 => {
            // Example 2
            vec![1, -1, 2, -1, -1]
        }
        9 => {
            // Max length, mostly -1
            build(100, rng, 80)
        }
        10 => {
            // Small random mostly -1
            let n = rng.gen_range_usize(1, 10);
            build(n, rng, 70)
        }
        _ => {
            let n = rng.gen_range_usize(1, 100);
            build(n, rng, 50)
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
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let vals = if t < modes * 3 {
            adversarial(t % modes, &mut rng)
        } else {
            let n = rng.gen_range_usize(1, 100);
            let p = rng.gen_range_usize(10, 70) as u32;
            build(n, &mut rng, p)
        };
        let nums = generate_test_case(&vals);
        print_json(&nums);
    }
}