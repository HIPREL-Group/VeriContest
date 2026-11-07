use vstd::prelude::*;

verus! {

pub fn generate_test_case(fillers: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= fillers.len() <= 1000,
        forall |i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 100_000,
    ensures
        1 <= nums.len() <= 1000,
        nums.len() == fillers.len(),
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100_000,
{
    let n = fillers.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut pos: usize = 0;

    while pos < n
        invariant
            n == fillers.len(),
            1 <= n <= 1000,
            0 <= pos <= n,
            nums.len() == pos,
            forall |i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 100_000,
            forall |k: int| 0 <= k < pos as int ==> #[trigger] nums[k] == fillers[k],
            forall |k: int| 0 <= k < pos as int ==> 1 <= #[trigger] nums[k] <= 100_000,
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

fn build_fillers(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // all ones
            for _ in 0..n {
                v.push(1);
            }
        }
        1 => {
            // all max
            for _ in 0..n {
                v.push(100_000);
            }
        }
        2 => {
            // ascending 1..
            for i in 0..n {
                let val = ((i as i32) % 100_000) + 1;
                v.push(val);
            }
        }
        3 => {
            // descending
            for i in 0..n {
                let val = 100_000 - ((i as i32) % 100_000);
                v.push(val.max(1));
            }
        }
        4 => {
            // random small
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 10));
            }
        }
        5 => {
            // random full range
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100_000));
            }
        }
        6 => {
            // alternating
            for i in 0..n {
                if i % 2 == 0 { v.push(1); } else { v.push(100_000); }
            }
        }
        7 => {
            // all same middle
            let x = rng.gen_range_i32(1, 100_000);
            for _ in 0..n {
                v.push(x);
            }
        }
        8 => {
            // palindrome-ish
            for i in 0..n {
                let d = if i < n - 1 - i { i } else { n - 1 - i };
                v.push(((d as i32) % 100_000) + 1);
            }
        }
        _ => {
            // mixed with peaks
            for i in 0..n {
                let val = if i == n / 2 { 100_000 } else { rng.gen_range_i32(1, 1000) };
                v.push(val);
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
    let total = 200usize;

    // include fixed tiny cases
    let tiny1 = generate_test_case(&vec![1i32]);
    print_json(&tiny1);
    let tiny2 = generate_test_case(&vec![10i32, 4, 8, 3]);
    print_json(&tiny2);

    for t in 0..total {
        let mode = t % modes;
        let n = match t % 13 {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => 1000,
            4 => 999,
            5 => 500,
            6 => 100,
            7 => 50,
            8 => 10,
            9 => 5,
            10 => rng.gen_range_usize(1, 1000),
            11 => rng.gen_range_usize(1, 100),
            _ => rng.gen_range_usize(1, 20),
        };
        let fillers = build_fillers(&mut rng, mode, n);
        let nums = generate_test_case(&fillers);
        print_json(&nums);
    }
}