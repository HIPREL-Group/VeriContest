use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    fillers: &Vec<i32>,
    big_idx: usize,
    k: i32,
) -> (nums: Vec<i32>)
    requires
        1 <= k <= 1_000_000_000,
        fillers.len() + 1 <= 50,
        big_idx <= fillers.len(),
        forall|i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 1_000_000_000,
    ensures
        1 <= nums.len() <= 50,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
        1 <= k <= 1_000_000_000,
        exists|i: int| 0 <= i < nums.len() && nums[i] >= k,
{
    let n: usize = fillers.len() + 1;
    let mut nums: Vec<i32> = Vec::new();
    let mut fi: usize = 0;
    let mut pos: usize = 0;

    while pos < n
        invariant
            n == fillers.len() + 1,
            1 <= n <= 50,
            0 <= pos <= n,
            nums.len() == pos,
            big_idx <= fillers.len(),
            1 <= k <= 1_000_000_000,
            fi == pos - (if big_idx < pos { 1usize } else { 0usize }),
            0 <= fi <= fillers.len(),
            forall|i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 1_000_000_000,
            forall|i: int| 0 <= i < pos as int ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
            big_idx < pos ==> nums[big_idx as int] == 1_000_000_000i32,
        decreases n - pos,
    {
        if pos == big_idx {
            nums.push(1_000_000_000i32);
        } else {
            assert(fi < fillers.len());
            nums.push(fillers[fi]);
            fi = fi + 1;
        }
        pos = pos + 1;
    }

    proof {
        assert(big_idx < n);
        assert(nums[big_idx as int] == 1_000_000_000i32);
        assert(nums[big_idx as int] >= k);
    }

    nums
}

}

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(1) }
    }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
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

fn make_test(rng: &mut Rng, mode: usize, t: usize) -> (Vec<i32>, i32, usize) {
    let n: usize = match mode {
        0 => 1,
        1 => 2,
        2 => 50,
        3 => rng.gen_range_usize(1, 50),
        4 => rng.gen_range_usize(1, 10),
        5 => 50,
        6 => 50,
        7 => rng.gen_range_usize(1, 50),
        8 => rng.gen_range_usize(1, 50),
        9 => rng.gen_range_usize(1, 50),
        _ => rng.gen_range_usize(1, 50),
    };

    let k: i32 = match mode {
        0 => 1,
        1 => 1_000_000_000,
        2 => rng.gen_range_i32(1, 1_000_000_000),
        3 => 1,
        4 => rng.gen_range_i32(1, 100),
        5 => rng.gen_range_i32(999_999_000, 1_000_000_000),
        6 => rng.gen_range_i32(1, 1_000_000_000),
        7 => rng.gen_range_i32(1, 1_000_000_000),
        8 => rng.gen_range_i32(1, 10),
        9 => rng.gen_range_i32(1, 1_000_000_000),
        _ => rng.gen_range_i32(1, 1_000_000_000),
    };

    let fcount = n - 1;
    let mut fillers: Vec<i32> = Vec::with_capacity(fcount);
    for _ in 0..fcount {
        let v: i32 = match mode {
            0 => rng.gen_range_i32(1, 1_000_000_000),
            1 => rng.gen_range_i32(1, 1_000_000_000),
            2 => rng.gen_range_i32(1, 1_000_000_000),
            3 => rng.gen_range_i32(1, 1_000_000_000),
            4 => rng.gen_range_i32(1, 50),
            5 => rng.gen_range_i32(1, 999_999_000),
            6 => {
                // all less than k
                let upper = if k > 1 { k - 1 } else { 1 };
                rng.gen_range_i32(1, upper)
            }
            7 => {
                // all >= k to test 0 answer
                rng.gen_range_i32(k, 1_000_000_000)
            }
            8 => 1,
            9 => if rng.next_u64() % 2 == 0 { 1 } else { 1_000_000_000 },
            _ => rng.gen_range_i32(1, 1_000_000_000),
        };
        fillers.push(v);
    }

    let big_idx = if fcount == 0 { 0 } else { rng.gen_range_usize(0, fcount) };
    let _ = t;
    (fillers, k, big_idx)
}

fn print_json(nums: &[i32], k: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("],\"k\":{}}}", k);
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
        let (fillers, k, big_idx) = make_test(&mut rng, mode, t);
        let nums = generate_test_case(&fillers, big_idx, k);
        print_json(&nums, k);
    }
}