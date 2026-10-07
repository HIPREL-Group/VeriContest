use vstd::prelude::*;

verus! {

pub fn generate_test_case(fillers: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        fillers.len() >= 1,
        fillers.len() <= 100_000,
    ensures
        nums.len() >= 1,
        nums.len() <= 100_000,
        nums.len() == fillers.len(),
        forall|i: int| 0 <= i < nums.len() ==> nums[i] == fillers[i],
{
    let n: usize = fillers.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut pos: usize = 0;

    while pos < n
        invariant
            n == fillers.len(),
            0 <= pos <= n,
            nums.len() == pos,
            forall|k: int| 0 <= k < pos as int ==> nums[k] == fillers[k],
        decreases n - pos,
    {
        nums.push(fillers[pos]);
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
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn make_random(rng: &mut Rng, n: usize, lo: i32, hi: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i32(lo, hi));
    }
    v
}

fn make_mode(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            // single element
            let n = 1;
            make_random(rng, n, -100, 100)
        }
        1 => {
            // all negatives
            let n = rng.gen_range_usize(1, 50);
            make_random(rng, n, i32::MIN, -1)
        }
        2 => {
            // all zeros
            let n = rng.gen_range_usize(1, 50);
            vec![0i32; n]
        }
        3 => {
            // perfect 1..=n
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push((i + 1) as i32);
            }
            v
        }
        4 => {
            // 1..=n with one missing replaced
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::with_capacity(n);
            let miss = rng.gen_range_usize(0, n - 1);
            for i in 0..n {
                if i == miss {
                    v.push(-1);
                } else {
                    v.push((i + 1) as i32);
                }
            }
            v
        }
        5 => {
            // large positives only
            let n = rng.gen_range_usize(1, 50);
            make_random(rng, n, 1_000_000, i32::MAX)
        }
        6 => {
            // duplicates
            let n = rng.gen_range_usize(1, 100);
            let v_val = rng.gen_range_i32(-5, 5);
            vec![v_val; n]
        }
        7 => {
            // extremes
            let n = rng.gen_range_usize(1, 20);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                let c = rng.gen_range_usize(0, 3);
                let x = match c {
                    0 => i32::MIN,
                    1 => i32::MAX,
                    2 => 0,
                    _ => 1,
                };
                v.push(x);
            }
            v
        }
        8 => {
            // shuffled 1..=n
            let n = rng.gen_range_usize(1, 200);
            let mut v: Vec<i32> = (1..=n as i32).collect();
            for i in (1..v.len()).rev() {
                let j = rng.gen_range_usize(0, i);
                v.swap(i, j);
            }
            v
        }
        9 => {
            // large n
            let n = 100_000;
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push((i as i32) + 2); // missing 1
            }
            v
        }
        _ => {
            // random mix
            let n = rng.gen_range_usize(1, 200 + (t % 100));
            make_random(rng, n, -1000, 1000)
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
    let modes = 11usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let fillers = make_mode(&mut rng, mode, t);
        if fillers.is_empty() || fillers.len() > 100_000 {
            continue;
        }
        let nums = generate_test_case(&fillers);
        print_json(&nums);
    }
}