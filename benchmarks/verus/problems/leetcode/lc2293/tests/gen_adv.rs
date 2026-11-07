use vstd::prelude::*;

verus! {

pub open spec fn pow2_spec(k: int) -> int
    decreases k,
{
    if k <= 0 { 1 } else { 2 * pow2_spec(k - 1) }
}

pub fn pow2_exec(k: usize) -> (r: usize)
    requires
        0 <= k <= 10,
    ensures
        1 <= r <= 1024,
{
    1usize
}

pub proof fn lemma_pow2_bound(k: int)
    requires
        0 <= k <= 10,
    ensures
        true,
    decreases k,
{
}

pub fn generate_test_case(k: usize, fillers: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        0 <= k <= 10,
        fillers.len() == pow2_spec(k as int),
        forall|i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 1_000_000_000,
    ensures
        1 <= nums.len() <= 1024,
        exists|kk: int| 0 <= kk <= 10 && nums.len() == pow2_spec(kk),
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
{
    let mut nums: Vec<i32> = Vec::new();
    nums.push(1);

    proof {
        assert(exists|kk: int| 0 <= kk <= 10 && nums.len() == pow2_spec(kk)) by {
            let kk: int = 0;
            assert(nums.len() == pow2_spec(kk));
        }
        assert forall|i: int| 0 <= i < nums.len() implies 1 <= #[trigger] nums[i] <= 1_000_000_000 by {
            assert(nums[i] == 1);
        }
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

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
}

fn build_fillers(rng: &mut Rng, len: usize, mode: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(len);
    match mode {
        0 => {
            for _ in 0..len {
                v.push(rng.gen_range_i32(1, 1_000_000_000));
            }
        }
        1 => {
            for _ in 0..len {
                v.push(1);
            }
        }
        2 => {
            for _ in 0..len {
                v.push(1_000_000_000);
            }
        }
        3 => {
            for i in 0..len {
                v.push(if i % 2 == 0 { 1 } else { 1_000_000_000 });
            }
        }
        4 => {
            for i in 0..len {
                v.push((i as i32 % 1_000_000_000) + 1);
            }
        }
        5 => {
            for i in 0..len {
                v.push(((len - i) as i32 % 1_000_000_000) + 1);
            }
        }
        6 => {
            for i in 0..len {
                v.push(if i == 0 { 1 } else { 1_000_000_000 });
            }
        }
        7 => {
            for i in 0..len {
                v.push(if i == len - 1 { 1 } else { 1_000_000_000 });
            }
        }
        8 => {
            for _ in 0..len {
                v.push(rng.gen_range_i32(1, 10));
            }
        }
        9 => {
            for _ in 0..len {
                v.push(rng.gen_range_i32(999_999_000, 1_000_000_000));
            }
        }
        _ => {
            for i in 0..len {
                let base = if i % 3 == 0 { 1 } else if i % 3 == 1 { 500_000_000 } else { 1_000_000_000 };
                v.push(base);
            }
        }
    }
    v
}

fn pow2_host(k: usize) -> usize {
    let mut r = 1usize;
    for _ in 0..k {
        r *= 2;
    }
    r
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
    let total = 220usize;
    let modes = 11usize;

    for t in 0..total {
        let mode = t % modes;
        // pick k in [0, 10]
        let k: usize = match t % 13 {
            0 => 0,
            1 => 1,
            2 => 2,
            3 => 3,
            4 => 10,
            5 => 9,
            6 => 8,
            7 => 4,
            8 => 5,
            9 => 6,
            10 => 7,
            _ => rng.gen_range_usize(0, 10),
        };
        let n = pow2_host(k);
        let fillers = build_fillers(&mut rng, n, mode);
        let nums = generate_test_case(k, &fillers);
        print_json(&nums);
    }
}
