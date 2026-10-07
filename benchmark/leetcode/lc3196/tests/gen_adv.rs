use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    len: usize,
    fillers: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= len <= 100000,
        fillers.len() == len,
        forall|i: int| 0 <= i < fillers.len() ==> -1_000_000_000 <= #[trigger] fillers[i] <= 1_000_000_000,
    ensures
        1 <= nums.len() <= 100000,
        forall|i: int| 0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            len == fillers.len(),
            nums.len() == i,
            forall|k: int| 0 <= k < i as int ==> nums[k] == fillers[k],
            forall|k: int| 0 <= k < fillers.len() ==> -1_000_000_000 <= #[trigger] fillers[k] <= 1_000_000_000,
        decreases len - i,
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

fn build_random(rng: &mut Rng, n: usize, lo: i32, hi: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i32(lo, hi));
    }
    v
}

fn build_alternating(n: usize, a: i32, b: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        v.push(if i % 2 == 0 { a } else { b });
    }
    v
}

fn build_constant(n: usize, c: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(c);
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

    let total = 220usize;
    for t in 0..total {
        let mode = t % 11;
        let fillers: Vec<i32> = match mode {
            0 => {
                // size 1
                vec![rng.gen_range_i32(-1_000_000_000, 1_000_000_000)]
            }
            1 => {
                // size 2
                build_random(&mut rng, 2, -1_000_000_000, 1_000_000_000)
            }
            2 => {
                // small random
                let n = rng.gen_range_usize(3, 20);
                build_random(&mut rng, n, -1_000_000_000, 1_000_000_000)
            }
            3 => {
                // alternating extreme
                let n = rng.gen_range_usize(2, 100);
                build_alternating(n, 1_000_000_000, -1_000_000_000)
            }
            4 => {
                // all zeros
                let n = rng.gen_range_usize(1, 100);
                build_constant(n, 0)
            }
            5 => {
                // all positive max
                let n = rng.gen_range_usize(1, 100);
                build_constant(n, 1_000_000_000)
            }
            6 => {
                // all negative max
                let n = rng.gen_range_usize(1, 100);
                build_constant(n, -1_000_000_000)
            }
            7 => {
                // medium random
                let n = rng.gen_range_usize(50, 500);
                build_random(&mut rng, n, -1000, 1000)
            }
            8 => {
                // large random
                let n = 100_000;
                build_random(&mut rng, n, -1_000_000_000, 1_000_000_000)
            }
            9 => {
                // small negative/positive mix
                let n = rng.gen_range_usize(1, 10);
                build_random(&mut rng, n, -5, 5)
            }
            _ => {
                // alternating sign small
                let n = rng.gen_range_usize(1, 50);
                build_alternating(n, 1, -1)
            }
        };
        let len = fillers.len();
        let nums = generate_test_case(len, &fillers);
        print_json(&nums);
    }
}