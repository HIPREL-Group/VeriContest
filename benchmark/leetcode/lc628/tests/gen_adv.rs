use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    fillers: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        fillers.len() >= 3,
        fillers.len() <= 10_000,
        forall|i: int| 0 <= i < fillers.len() ==> -1000 <= #[trigger] fillers[i] <= 1000,
    ensures
        nums.len() >= 3,
        nums.len() <= 10_000,
        forall|i: int| 0 <= i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
{
    let n: usize = fillers.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut pos: usize = 0;

    while pos < n
        invariant
            n == fillers.len(),
            n >= 3,
            n <= 10_000,
            pos <= n,
            nums.len() == pos,
            forall|i: int| 0 <= i < fillers.len() ==> -1000 <= #[trigger] fillers[i] <= 1000,
            forall|k: int| 0 <= k < pos as int ==> nums[k] == fillers[k],
            forall|k: int| 0 <= k < pos as int ==> -1000 <= #[trigger] nums[k] <= 1000,
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
        Self { state: seed.wrapping_add(1) }
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

fn make_nums(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // all positives
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 1000));
            }
        }
        1 => {
            // all negatives
            for _ in 0..n {
                v.push(rng.gen_range_i32(-1000, -1));
            }
        }
        2 => {
            // mix
            for _ in 0..n {
                v.push(rng.gen_range_i32(-1000, 1000));
            }
        }
        3 => {
            // two large negatives + positives
            v.push(-1000);
            v.push(-1000);
            for _ in 2..n {
                v.push(rng.gen_range_i32(1, 1000));
            }
        }
        4 => {
            // all zeros
            for _ in 0..n {
                v.push(0);
            }
        }
        5 => {
            // boundary values
            for i in 0..n {
                v.push(if i % 3 == 0 { 1000 } else if i % 3 == 1 { -1000 } else { 0 });
            }
        }
        6 => {
            // small values near zero
            for _ in 0..n {
                v.push(rng.gen_range_i32(-3, 3));
            }
        }
        7 => {
            // one big positive, rest negative
            v.push(1000);
            for _ in 1..n {
                v.push(rng.gen_range_i32(-1000, -1));
            }
        }
        8 => {
            // two big negatives, rest small
            v.push(-1000);
            v.push(-999);
            for _ in 2..n {
                v.push(rng.gen_range_i32(0, 10));
            }
        }
        9 => {
            // three negatives only
            for _ in 0..n {
                v.push(rng.gen_range_i32(-1000, -990));
            }
        }
        _ => {
            // completely random
            for _ in 0..n {
                v.push(rng.gen_range_i32(-1000, 1000));
            }
        }
    }
    // ensure all in range [-1000, 1000]
    for x in v.iter_mut() {
        if *x < -1000 {
            *x = -1000;
        }
        if *x > 1000 {
            *x = 1000;
        }
    }
    v
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
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n: usize = match mode {
            0 => 3 + (t % 5),
            1 => 3 + (t % 7),
            2 => 10 + (t % 50),
            3 => 3 + (t % 10),
            4 => 3 + (t % 4),
            5 => 3 + (t % 20),
            6 => 5 + (t % 30),
            7 => 3 + (t % 15),
            8 => 3 + (t % 10),
            9 => 3,
            _ => 100 + (t % 200),
        };
        let n = if n < 3 { 3 } else if n > 10_000 { 10_000 } else { n };

        let fillers = make_nums(&mut rng, mode, n);
        let nums = generate_test_case(&fillers);
        print_json(&nums);
    }
}