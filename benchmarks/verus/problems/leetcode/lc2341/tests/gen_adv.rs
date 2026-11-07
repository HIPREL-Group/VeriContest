use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 100,
        forall |i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 100,
    ensures
        1 <= nums.len() <= 100,
        forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 100,
{
    let n: usize = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut pos: usize = 0;

    while pos < n
        invariant
            n == values.len(),
            1 <= n <= 100,
            0 <= pos <= n,
            nums.len() == pos,
            forall |i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 100,
            forall |k: int| 0 <= k < pos as int ==> #[trigger] nums[k] == values[k],
            forall |k: int| 0 <= k < pos as int ==> 0 <= #[trigger] nums[k] <= 100,
        decreases n - pos,
    {
        nums.push(values[pos]);
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
        Self { state: seed.wrapping_add(0x9E3779B97F4A7C15) }
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

fn build_values(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            // minimal size 1
            vec![rng.gen_range_i32(0, 100)]
        }
        1 => {
            // max size, all same
            let v = rng.gen_range_i32(0, 100);
            vec![v; 100]
        }
        2 => {
            // max size, all distinct (values 0..99 or similar)
            let mut v = Vec::new();
            for i in 0..100 {
                v.push((i % 101) as i32);
            }
            v
        }
        3 => {
            // all zeros
            let n = rng.gen_range_usize(1, 100);
            vec![0i32; n]
        }
        4 => {
            // all 100
            let n = rng.gen_range_usize(1, 100);
            vec![100i32; n]
        }
        5 => {
            // pairs of same value
            let pairs = rng.gen_range_usize(1, 50);
            let mut v = Vec::new();
            for _ in 0..pairs {
                let x = rng.gen_range_i32(0, 100);
                v.push(x);
                v.push(x);
            }
            v
        }
        6 => {
            // odd count with pairs + one leftover
            let pairs = rng.gen_range_usize(0, 49);
            let mut v = Vec::new();
            for _ in 0..pairs {
                let x = rng.gen_range_i32(0, 100);
                v.push(x);
                v.push(x);
            }
            v.push(rng.gen_range_i32(0, 100));
            v
        }
        7 => {
            // two elements
            vec![rng.gen_range_i32(0, 100), rng.gen_range_i32(0, 100)]
        }
        8 => {
            // triples - tests handling of odd counts per value
            let trips = rng.gen_range_usize(1, 33);
            let mut v = Vec::new();
            for _ in 0..trips {
                let x = rng.gen_range_i32(0, 100);
                v.push(x);
                v.push(x);
                v.push(x);
            }
            v
        }
        9 => {
            // random size, random values
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 100));
            }
            v
        }
        _ => {
            // alternating two values
            let n = rng.gen_range_usize(1, 100);
            let a = rng.gen_range_i32(0, 100);
            let b = rng.gen_range_i32(0, 100);
            let mut v = Vec::new();
            for i in 0..n {
                v.push(if i % 2 == 0 { a } else { b });
            }
            let _ = t;
            v
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
        let values = build_values(&mut rng, mode, t);
        // Ensure constraints: 1 <= len <= 100 and values in [0,100]
        let mut clamped: Vec<i32> = Vec::new();
        for &x in &values {
            let v = if x < 0 { 0 } else if x > 100 { 100 } else { x };
            clamped.push(v);
            if clamped.len() == 100 {
                break;
            }
        }
        if clamped.is_empty() {
            clamped.push(0);
        }
        let nums = generate_test_case(&clamped);
        print_json(&nums);
    }
}