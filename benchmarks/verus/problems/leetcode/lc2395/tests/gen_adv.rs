use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    fillers: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        2 <= fillers.len() <= 1000,
        forall|i: int| 0 <= i < fillers.len() ==> -1_000_000_000 <= #[trigger] fillers[i] <= 1_000_000_000,
    ensures
        2 <= nums.len() <= 1000,
        forall|i: int| 0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
{
    let n = fillers.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == fillers.len(),
            0 <= i <= n,
            nums.len() == i,
            forall|k: int| 0 <= k < i as int ==> #[trigger] nums[k] == fillers[k],
            forall|k: int| 0 <= k < fillers.len() ==> -1_000_000_000 <= #[trigger] fillers[k] <= 1_000_000_000,
        decreases n - i,
    {
        nums.push(fillers[i]);
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

fn build_mode(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            // small random
            let n = rng.gen_range_usize(2, 10);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(-1_000_000_000, 1_000_000_000));
            }
            v
        }
        1 => {
            // all zeros - many equal sums
            let n = rng.gen_range_usize(2, 50);
            vec![0i32; n]
        }
        2 => {
            // strictly increasing - likely no equal pair sums
            let n = rng.gen_range_usize(2, 100);
            let start = rng.gen_range_i32(-1000, 1000);
            let mut v = Vec::new();
            for i in 0..n {
                v.push(start + i as i32);
            }
            v
        }
        3 => {
            // length exactly 2
            vec![rng.gen_range_i32(-1_000_000_000, 1_000_000_000),
                 rng.gen_range_i32(-1_000_000_000, 1_000_000_000)]
        }
        4 => {
            // length exactly 3 - at most 2 subarrays
            vec![rng.gen_range_i32(-100, 100),
                 rng.gen_range_i32(-100, 100),
                 rng.gen_range_i32(-100, 100)]
        }
        5 => {
            // maximum length
            let n = 1000;
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(-1_000_000_000, 1_000_000_000));
            }
            v
        }
        6 => {
            // extreme values
            let n = rng.gen_range_usize(2, 20);
            let mut v = Vec::new();
            for _ in 0..n {
                if rng.next_u64() % 2 == 0 {
                    v.push(1_000_000_000);
                } else {
                    v.push(-1_000_000_000);
                }
            }
            v
        }
        7 => {
            // [a, b, b, a] pattern - has equal sums
            let a = rng.gen_range_i32(-500_000_000, 500_000_000);
            let b = rng.gen_range_i32(-500_000_000, 500_000_000);
            vec![a, b, b, a]
        }
        8 => {
            // [4,2,4] example-like
            let x = rng.gen_range_i32(-1000, 1000);
            let y = rng.gen_range_i32(-1000, 1000);
            vec![x, y, x]
        }
        9 => {
            // arithmetic progression (no equal adjacent sums)
            let n = rng.gen_range_usize(5, 50);
            let d = rng.gen_range_i32(1, 100);
            let s = rng.gen_range_i32(-1000, 1000);
            let mut v = Vec::new();
            for i in 0..n {
                v.push(s + d * i as i32);
            }
            v
        }
        _ => {
            // random large
            let n = rng.gen_range_usize(100, 1000);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(-1_000_000_000, 1_000_000_000));
            }
            v
        }
    }
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
    } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;
    for t in 0..total {
        let mode = t % modes;
        let fillers = build_mode(&mut rng, mode, t);
        if fillers.len() < 2 || fillers.len() > 1000 { continue; }
        let mut ok = true;
        for &x in &fillers {
            if x < -1_000_000_000 || x > 1_000_000_000 { ok = false; break; }
        }
        if !ok { continue; }
        let nums = generate_test_case(&fillers);
        print_json(&nums);
    }
}