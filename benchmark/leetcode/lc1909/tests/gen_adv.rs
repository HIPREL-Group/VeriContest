use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        2 <= values.len() <= 1000,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1000,
    ensures
        2 <= nums.len() <= 1000,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            2 <= n <= 1000,
            0 <= i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < i as int ==> #[trigger] nums[k] == values[k],
            forall |k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 1000,
        decreases n - i,
    {
        nums.push(values[i]);
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
}

fn clamp_vec(v: &mut Vec<i32>) {
    for x in v.iter_mut() {
        if *x < 1 { *x = 1; }
        if *x > 1000 { *x = 1000; }
    }
}

fn make_case(rng: &mut Rng, mode: usize) -> Vec<i32> {
    let n = match mode {
        0 => 2,
        1 => 3,
        2 => rng.gen_range_usize(2, 10),
        3 => rng.gen_range_usize(2, 100),
        4 => 1000,
        5 => rng.gen_range_usize(2, 1000),
        6 => rng.gen_range_usize(2, 50),
        7 => rng.gen_range_usize(2, 50),
        8 => rng.gen_range_usize(2, 50),
        9 => rng.gen_range_usize(2, 50),
        _ => rng.gen_range_usize(2, 1000),
    };

    let mut v: Vec<i32> = Vec::with_capacity(n);

    match mode {
        0 | 1 => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 1000));
            }
        }
        2 => {
            // strictly increasing
            let mut cur = 1i32;
            for _ in 0..n {
                v.push(cur);
                cur += rng.gen_range_i32(1, 5);
                if cur > 1000 { cur = 1000; }
            }
        }
        3 => {
            // strictly increasing with one duplicate
            let mut cur = 1i32;
            for _ in 0..n {
                v.push(cur);
                cur += rng.gen_range_i32(1, 3);
                if cur > 1000 { cur = 1000; }
            }
            if n >= 2 {
                let idx = rng.gen_range_usize(1, n - 1);
                v[idx] = v[idx - 1];
            }
        }
        4 => {
            // all equal
            let x = rng.gen_range_i32(1, 1000);
            for _ in 0..n {
                v.push(x);
            }
        }
        5 => {
            // strictly decreasing
            let mut cur = 1000i32;
            for _ in 0..n {
                v.push(cur);
                cur -= rng.gen_range_i32(1, 3);
                if cur < 1 { cur = 1; }
            }
        }
        6 => {
            // one spike that can be removed
            let mut cur = 1i32;
            for _ in 0..n {
                v.push(cur);
                cur += rng.gen_range_i32(1, 3);
                if cur > 1000 { cur = 1000; }
            }
            if n >= 3 {
                let idx = rng.gen_range_usize(1, n - 2);
                v[idx] = 1000;
            }
        }
        7 => {
            // small dip that can be removed
            let mut cur = 10i32;
            for _ in 0..n {
                v.push(cur);
                cur += rng.gen_range_i32(1, 5);
                if cur > 1000 { cur = 1000; }
            }
            if n >= 3 {
                let idx = rng.gen_range_usize(1, n - 2);
                v[idx] = 1;
            }
        }
        8 => {
            // two problems — should fail
            let mut cur = 1i32;
            for _ in 0..n {
                v.push(cur);
                cur += rng.gen_range_i32(1, 3);
                if cur > 1000 { cur = 1000; }
            }
            if n >= 4 {
                v[1] = 1000;
                v[n - 2] = 1;
            }
        }
        9 => {
            // alternating
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(rng.gen_range_i32(1, 500));
                } else {
                    v.push(rng.gen_range_i32(501, 1000));
                }
            }
        }
        _ => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 1000));
            }
        }
    }

    clamp_vec(&mut v);
    if v.len() < 2 {
        v.push(1);
        v.push(2);
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
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let values = make_case(&mut rng, mode);
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}