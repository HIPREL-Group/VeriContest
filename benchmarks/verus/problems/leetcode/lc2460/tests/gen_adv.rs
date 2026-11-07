use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        2 <= values.len() <= 2000,
        forall |i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 1000,
    ensures
        2 <= nums.len() <= 2000,
        forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1000,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            nums.len() == i,
            forall |k: int| 0 <= k < values.len() ==> 0 <= #[trigger] values[k] <= 1000,
            forall |k: int| 0 <= k < i as int ==> nums[k] == values[k],
            forall |k: int| 0 <= k < i as int ==> 0 <= #[trigger] nums[k] <= 1000,
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
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn clamp(v: i32) -> i32 {
    if v < 0 { 0 } else if v > 1000 { 1000 } else { v }
}

fn make_mode(rng: &mut Rng, mode: usize) -> Vec<i32> {
    match mode {
        0 => {
            // minimal length 2
            let a = rng.gen_range_i32(0, 1000);
            let b = rng.gen_range_i32(0, 1000);
            vec![a, b]
        }
        1 => {
            // all zeros
            let n = rng.gen_range_usize(2, 100);
            vec![0i32; n]
        }
        2 => {
            // all equal non-zero
            let n = rng.gen_range_usize(2, 200);
            let v = rng.gen_range_i32(1, 500);
            vec![v; n]
        }
        3 => {
            // max length
            let n = 2000usize;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1000));
            }
            v
        }
        4 => {
            // many adjacent equals
            let n = rng.gen_range_usize(2, 500);
            let mut v = Vec::with_capacity(n);
            let mut i = 0;
            while i < n {
                let x = rng.gen_range_i32(0, 1000);
                v.push(x);
                if i + 1 < n {
                    v.push(x);
                    i += 2;
                } else {
                    i += 1;
                }
            }
            v
        }
        5 => {
            // zeros interspersed
            let n = rng.gen_range_usize(2, 300);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                if rng.gen_range_usize(0, 2) == 0 {
                    v.push(0);
                } else {
                    let _ = i;
                    v.push(rng.gen_range_i32(1, 100));
                }
            }
            v
        }
        6 => {
            // all 1000 - boundary values
            let n = rng.gen_range_usize(2, 500);
            vec![1000i32; n]
        }
        7 => {
            // alternating a,b,a,b
            let n = rng.gen_range_usize(2, 500);
            let a = rng.gen_range_i32(0, 1000);
            let b = rng.gen_range_i32(0, 1000);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push(if i % 2 == 0 { a } else { b });
            }
            v
        }
        8 => {
            // pattern causing chain operations like [1,1,1,1]
            let n = rng.gen_range_usize(2, 200);
            let base = rng.gen_range_i32(1, 10);
            vec![base; n]
        }
        9 => {
            // sparse with one pair
            let n = rng.gen_range_usize(3, 500);
            let mut v = vec![0i32; n];
            let i = rng.gen_range_usize(0, n - 2);
            let x = rng.gen_range_i32(1, 1000);
            v[i] = x;
            v[i + 1] = x;
            v
        }
        _ => {
            let n = rng.gen_range_usize(2, 2000);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1000));
            }
            v
        }
    }
}

fn sanitize(v: Vec<i32>) -> Vec<i32> {
    let mut out: Vec<i32> = v.into_iter().map(clamp).collect();
    if out.len() < 2 {
        while out.len() < 2 {
            out.push(0);
        }
    }
    if out.len() > 2000 {
        out.truncate(2000);
    }
    out
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
        let raw = make_mode(&mut rng, mode);
        let values = sanitize(raw);
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}