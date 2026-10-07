use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    l_val: i32,
    r_val: i32,
    vals: &Vec<i32>,
) -> (result: (Vec<i32>, i32, i32))
    requires
        1 <= n <= 100,
        vals.len() == n,
        1 <= l_val <= r_val,
        r_val as int <= n as int,
        forall|i: int| 0 <= i < vals.len() ==> -1000 <= #[trigger] vals[i] <= 1000,
    ensures
        ({
            let nums = result.0;
            let l = result.1;
            let r = result.2;
            &&& 1 <= nums.len() <= 100
            &&& 1 <= l <= r
            &&& r as int <= nums.len() as int
            &&& l == l_val
            &&& r == r_val
            &&& (forall|i: int| 0 <= i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000)
        }),
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            nums.len() == i,
            vals.len() == n,
            forall|k: int| 0 <= k < vals.len() ==> -1000 <= #[trigger] vals[k] <= 1000,
            forall|k: int| 0 <= k < i as int ==> nums[k] == vals[k],
        decreases n - i,
    {
        let v = vals[i];
        nums.push(v);
        i = i + 1;
    }

    assert(nums.len() == n);
    assert forall|k: int| 0 <= k < nums.len() implies -1000 <= #[trigger] nums[k] <= 1000 by {
        assert(nums[k] == vals[k]);
    }

    (nums, l_val, r_val)
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
        self.state = self
            .state
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

fn build_vals(rng: &mut Rng, n: usize, mode: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(-1000, 1000));
            }
        }
        1 => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(-1000, -1));
            }
        }
        2 => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 1000));
            }
        }
        3 => {
            for _ in 0..n {
                v.push(0);
            }
        }
        4 => {
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(1000);
                } else {
                    v.push(-1000);
                }
            }
        }
        5 => {
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(1);
                } else {
                    v.push(-1);
                }
            }
        }
        6 => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(-5, 5));
            }
        }
        7 => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(-2, 2));
            }
        }
        8 => {
            // one big pos surrounded by negatives
            for i in 0..n {
                if i == n / 2 {
                    v.push(1000);
                } else {
                    v.push(rng.gen_range_i32(-1000, -1));
                }
            }
        }
        9 => {
            // extremes
            for i in 0..n {
                if i % 3 == 0 {
                    v.push(1000);
                } else if i % 3 == 1 {
                    v.push(-1000);
                } else {
                    v.push(0);
                }
            }
        }
        _ => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(-10, 10));
            }
        }
    }
    v
}

fn print_json(nums: &[i32], l: i32, r: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", nums[i]);
    }
    println!("],\"l\":{},\"r\":{}}}", l, r);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };
    let mut rng = Rng::new(seed);
    let total = 200usize;
    let modes = 11usize;

    for t in 0..total {
        let mode = t % modes;
        let n: usize = match t % 7 {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => 10,
            4 => 50,
            5 => 100,
            _ => rng.gen_range_usize(1, 100),
        };
        let vals = build_vals(&mut rng, n, mode);
        let l = rng.gen_range_usize(1, n) as i32;
        let r = rng.gen_range_usize(l as usize, n) as i32;
        let (nums, ll, rr) = generate_test_case(n, l, r, &vals);
        print_json(&nums, ll, rr);
    }
}