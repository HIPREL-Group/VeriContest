use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    l: usize,
    r: usize,
    fillers: &Vec<i32>,
) -> (res: (Vec<i32>, usize, usize))
    requires
        1 <= n <= 100_000,
        l <= r,
        r < n,
        fillers.len() == n,
    ensures
        res.1 <= res.2,
        res.2 < res.0.len(),
        1 <= res.0.len() <= 100_000,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            nums.len() == i,
            fillers.len() == n,
            1 <= n <= 100_000,
        decreases n - i,
    {
        nums.push(fillers[i]);
        i = i + 1;
    }
    (nums, l, r)
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

fn print_json(nums: &[i32], l: usize, r: usize) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", nums[i]);
    }
    println!("],\"l\":{},\"r\":{}}}", l, r);
}

fn make_fillers(rng: &mut Rng, n: usize, mode: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        let x = match mode {
            0 => rng.gen_range_i32(-100, 100),
            1 => 0i32,
            2 => i32::MIN,
            3 => i32::MAX,
            4 => i as i32,
            5 => (n - i) as i32,
            6 => if i % 2 == 0 { i32::MIN } else { i32::MAX },
            7 => rng.gen_range_i32(i32::MIN, i32::MAX),
            8 => rng.gen_range_i32(-5, 5),
            _ => (i as i32) - (n as i32 / 2),
        };
        v.push(x);
    }
    v
}

fn pick_lr(rng: &mut Rng, n: usize, mode: usize) -> (usize, usize) {
    match mode {
        0 => (0, n - 1),
        1 => (0, 0),
        2 => (n - 1, n - 1),
        3 => (0, if n >= 2 { 1 } else { 0 }),
        4 => {
            let mid = n / 2;
            (mid, mid)
        }
        5 => (0, n / 2),
        6 => (n / 2, n - 1),
        _ => {
            let a = rng.gen_range_usize(0, n - 1);
            let b = rng.gen_range_usize(0, n - 1);
            if a <= b { (a, b) } else { (b, a) }
        }
    }
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
    let modes = 10usize;

    for t in 0..total {
        let fmode = t % modes;
        let lmode = (t / modes) % 8;
        let n = match t % 12 {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => 10,
            4 => 100,
            5 => 1000,
            6 => 100_000,
            7 => 50_000,
            8 => 99_999,
            9 => 5,
            10 => 256,
            _ => rng.gen_range_usize(1, 500),
        };
        let fillers = make_fillers(&mut rng, n, fmode);
        let (l, r) = pick_lr(&mut rng, n, lmode);
        let (nums, l2, r2) = generate_test_case(n, l, r, &fillers);
        print_json(&nums, l2, r2);
    }
}