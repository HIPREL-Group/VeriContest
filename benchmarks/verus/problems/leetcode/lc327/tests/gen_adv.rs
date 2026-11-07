use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    nums_filler: &Vec<i32>,
    lower: i32,
    upper: i32,
) -> (result: (Vec<i64>, Vec<i64>, usize, usize, i64, i64))
    requires
        1 <= n <= 100000,
        nums_filler.len() == n,
        forall|i: int| 0 <= i < nums_filler.len() ==> -2147483648 <= #[trigger] nums_filler[i] <= 2147483647,
        -100000 <= lower as int <= upper as int <= 100000,
    ensures
        ({
            let (sums, buf, l, r, lo, up) = result;
            sums.len() == n + 1
            && buf.len() == n + 1
            && l == 0
            && r == n
            && lo as int == lower as int
            && up as int == upper as int
        }),
{
    let mut sums: Vec<i64> = Vec::new();
    let mut buf: Vec<i64> = Vec::new();
    sums.push(0i64);
    buf.push(0i64);
    let total = n;
    let mut i: usize = 0;
    while i < total
        invariant
            i <= total,
            sums.len() == i + 1,
            buf.len() == i + 1,
        decreases total - i,
    {
        sums.push(0i64);
        buf.push(0i64);
        i = i + 1;
    }

    (sums, buf, 0usize, n, lower as i64, upper as i64)
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

fn pick_nums(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    match mode {
        0 => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(-100, 100));
            }
        }
        1 => {
            for _ in 0..n {
                v.push(0);
            }
        }
        2 => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(i32::MIN, i32::MAX));
            }
        }
        3 => {
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(i32::MAX);
                } else {
                    v.push(i32::MIN);
                }
            }
        }
        4 => {
            for _ in 0..n {
                v.push(i32::MAX);
            }
        }
        5 => {
            for _ in 0..n {
                v.push(i32::MIN);
            }
        }
        6 => {
            for i in 0..n {
                v.push(if i % 2 == 0 { 1 } else { -1 });
            }
        }
        7 => {
            for i in 0..n {
                v.push((i as i32) - (n as i32) / 2);
            }
        }
        8 => {
            for _ in 0..n {
                if rng.next_u64() % 2 == 0 {
                    v.push(rng.gen_range_i32(-5, 5));
                } else {
                    v.push(rng.gen_range_i32(i32::MIN, i32::MAX));
                }
            }
        }
        9 => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(-3, 3));
            }
        }
        _ => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(-1000, 1000));
            }
        }
    }
    v
}

fn pick_bounds(rng: &mut Rng, mode: usize) -> (i32, i32) {
    let mode2 = mode % 5;
    match mode2 {
        0 => {
            let a = rng.gen_range_i32(-100000, 100000);
            let b = rng.gen_range_i32(-100000, 100000);
            if a <= b { (a, b) } else { (b, a) }
        }
        1 => {
            let x = rng.gen_range_i32(-100000, 100000);
            (x, x)
        }
        2 => (-100000, 100000),
        3 => (0, 0),
        _ => {
            let a = rng.gen_range_i32(-10, 10);
            let b = rng.gen_range_i32(-10, 10);
            if a <= b { (a, b) } else { (b, a) }
        }
    }
}

fn print_json(nums: &[i32], lower: i32, upper: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("],\"lower\":{},\"upper\":{}}}", lower, upper);
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

    for t in 0..total {
        let mode = t % 10;
        let n = match t % 7 {
            0 => 1,
            1 => 2,
            2 => 10,
            3 => 100,
            4 => 1000,
            5 => 5000,
            _ => {
                let choice = rng.next_u64() % 100;
                if choice < 10 { 1 + (rng.next_u64() as usize % 10) }
                else if choice < 50 { 1 + (rng.next_u64() as usize % 500) }
                else { 1 + (rng.next_u64() as usize % 3000) }
            }
        };

        let nums = pick_nums(&mut rng, mode, n);
        let (lower, upper) = pick_bounds(&mut rng, t);

        let _ = generate_test_case(n, &nums, lower, upper);
        print_json(&nums, lower, upper);
    }
}
