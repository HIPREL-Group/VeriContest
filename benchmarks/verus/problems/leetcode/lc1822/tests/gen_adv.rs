use vstd::prelude::*;

verus! {

pub fn generate_test_case(vals: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= vals.len() <= 1000,
        forall |i: int| 0 <= i < vals.len() ==> -100 <= #[trigger] vals[i] <= 100,
    ensures
        1 <= nums.len() <= 1000,
        forall |i: int| 0 <= i < nums.len() ==> -100 <= #[trigger] nums[i] <= 100,
{
    let n = vals.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            n == vals.len(),
            1 <= n <= 1000,
            0 <= k <= n,
            nums.len() == k,
            forall |i: int| 0 <= i < vals.len() ==> -100 <= #[trigger] vals[i] <= 100,
            forall |i: int| 0 <= i < k as int ==> nums[i] == vals[i],
            forall |i: int| 0 <= i < k as int ==> -100 <= #[trigger] nums[i] <= 100,
        decreases n - k,
    {
        nums.push(vals[k]);
        k = k + 1;
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

fn make_vals(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    match mode {
        0 => {
            // small random all positive
            let n = rng.gen_range_usize(1, 20);
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100));
            }
        }
        1 => {
            // random with a zero
            let n = rng.gen_range_usize(2, 50);
            for _ in 0..n {
                v.push(rng.gen_range_i32(-100, 100));
            }
            let idx = rng.gen_range_usize(0, n - 1);
            v[idx] = 0;
        }
        2 => {
            // all negatives
            let n = rng.gen_range_usize(1, 30);
            for _ in 0..n {
                v.push(rng.gen_range_i32(-100, -1));
            }
        }
        3 => {
            // single element
            v.push(rng.gen_range_i32(-100, 100));
        }
        4 => {
            // exactly zero element
            v.push(0);
        }
        5 => {
            // max length
            for i in 0..1000 {
                let x = rng.gen_range_i32(-100, 100);
                let _ = i;
                v.push(x);
            }
        }
        6 => {
            // max length all non-zero (alternating sign)
            for i in 0..1000 {
                if i % 2 == 0 {
                    v.push(rng.gen_range_i32(1, 100));
                } else {
                    v.push(rng.gen_range_i32(-100, -1));
                }
            }
        }
        7 => {
            // many zeros
            let n = rng.gen_range_usize(5, 100);
            for _ in 0..n {
                if rng.next_u64() % 3 == 0 {
                    v.push(0);
                } else {
                    v.push(rng.gen_range_i32(-100, 100));
                }
            }
        }
        8 => {
            // all ones and minus ones
            let n = rng.gen_range_usize(1, 500);
            for _ in 0..n {
                if rng.next_u64() % 2 == 0 {
                    v.push(1);
                } else {
                    v.push(-1);
                }
            }
        }
        9 => {
            // boundary +/-100
            let n = rng.gen_range_usize(1, 100);
            for _ in 0..n {
                let r = rng.next_u64() % 3;
                if r == 0 {
                    v.push(100);
                } else if r == 1 {
                    v.push(-100);
                } else {
                    v.push(0);
                }
            }
        }
        _ => {
            let n = rng.gen_range_usize(1, 1000);
            for _ in 0..n {
                v.push(rng.gen_range_i32(-100, 100));
            }
        }
    }
    let _ = t;
    if v.is_empty() {
        v.push(0);
    }
    if v.len() > 1000 {
        v.truncate(1000);
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
        let vals = make_vals(&mut rng, mode, t);
        let nums = generate_test_case(&vals);
        print_json(&nums);
    }
}