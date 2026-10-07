use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 10_000,
        forall |i: int| 0 <= i < values.len() ==> -10_000 <= #[trigger] values[i] <= 10_000,
        forall |i: int, j: int| 0 <= i <= j < values.len() ==> values[i] <= values[j],
    ensures
        1 <= nums.len() <= 10_000,
        forall |i: int| 0 <= i < nums.len() ==> -10_000 <= #[trigger] nums[i] <= 10_000,
        forall |i: int, j: int| 0 <= i <= j < nums.len() ==> nums[i] <= nums[j],
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            n == values.len(),
            0 <= k <= n,
            nums.len() == k,
            forall |i: int| 0 <= i < k as int ==> nums[i] == values[i],
            forall |i: int| 0 <= i < values.len() ==> -10_000 <= #[trigger] values[i] <= 10_000,
            forall |i: int, j: int| 0 <= i <= j < values.len() ==> values[i] <= values[j],
        decreases n - k,
    {
        nums.push(values[k]);
        k = k + 1;
    }
    nums
}

}

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

fn make_sorted(rng: &mut Rng, n: usize, lo: i32, hi: i32) -> Vec<i32> {
    let mut v: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(lo, hi)).collect();
    v.sort();
    v
}

fn make_test(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            // single element
            vec![rng.gen_range_i32(-10_000, 10_000)]
        }
        1 => {
            // all negatives
            let n = rng.gen_range_usize(1, 20);
            make_sorted(rng, n, -10_000, -1)
        }
        2 => {
            // all positives
            let n = rng.gen_range_usize(1, 20);
            make_sorted(rng, n, 1, 10_000)
        }
        3 => {
            // all zeros
            let n = rng.gen_range_usize(1, 50);
            vec![0; n]
        }
        4 => {
            // mixed negatives and positives
            let n = rng.gen_range_usize(2, 50);
            make_sorted(rng, n, -10_000, 10_000)
        }
        5 => {
            // extremes
            let n = rng.gen_range_usize(2, 10);
            let mut v: Vec<i32> = Vec::new();
            for _ in 0..n {
                let choice = rng.next_u64() % 3;
                let val = match choice {
                    0 => -10_000,
                    1 => 0,
                    _ => 10_000,
                };
                v.push(val);
            }
            v.sort();
            v
        }
        6 => {
            // large n
            let n = 10_000;
            make_sorted(rng, n, -10_000, 10_000)
        }
        7 => {
            // duplicates
            let n = rng.gen_range_usize(2, 30);
            let val = rng.gen_range_i32(-10_000, 10_000);
            vec![val; n]
        }
        8 => {
            // around zero (negatives and positives that square to same)
            let n = rng.gen_range_usize(2, 20);
            let mut v: Vec<i32> = Vec::new();
            for _ in 0..n {
                let x = rng.gen_range_i32(1, 100);
                if rng.next_u64() % 2 == 0 {
                    v.push(-x);
                } else {
                    v.push(x);
                }
            }
            v.sort();
            v
        }
        9 => {
            // small size variations
            let n = 2 + (t % 5);
            make_sorted(rng, n, -50, 50)
        }
        _ => {
            let n = rng.gen_range_usize(1, 100);
            make_sorted(rng, n, -10_000, 10_000)
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
    let total = 220usize;
    for t in 0..total {
        let mode = t % modes;
        let values = make_test(&mut rng, mode, t);
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}