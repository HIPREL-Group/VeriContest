use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    nums_in: &Vec<i32>,
    change_indices_in: &Vec<i32>,
    t_in: usize,
) -> (res: (Vec<i32>, Vec<i32>, usize))
    requires
        1 <= nums_in.len() <= 2000,
        1 <= change_indices_in.len() <= 2000,
        1 <= t_in <= change_indices_in.len(),
        forall|i: int| 0 <= i < nums_in.len() ==> 0 <= #[trigger] nums_in[i] <= 1_000_000_000,
        forall|i: int| 0 <= i < change_indices_in.len() ==> 1 <= #[trigger] change_indices_in[i] <= nums_in.len(),
    ensures
        1 <= res.0.len() <= 2000,
        1 <= res.1.len() <= 2000,
        1 <= res.2 <= res.1.len(),
        forall|i: int| 0 <= i < res.0.len() ==> 0 <= #[trigger] res.0[i] <= 1_000_000_000,
        forall|i: int| 0 <= i < res.1.len() ==> 1 <= #[trigger] res.1[i] <= res.0.len(),
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < nums_in.len()
        invariant
            0 <= i <= nums_in.len(),
            nums.len() == i,
            forall|k: int| 0 <= k < i as int ==> nums[k] == nums_in[k],
            forall|k: int| 0 <= k < nums_in.len() ==> 0 <= #[trigger] nums_in[k] <= 1_000_000_000,
        decreases nums_in.len() - i,
    {
        nums.push(nums_in[i]);
        i = i + 1;
    }

    let mut ci: Vec<i32> = Vec::new();
    let mut j: usize = 0;
    while j < change_indices_in.len()
        invariant
            0 <= j <= change_indices_in.len(),
            ci.len() == j,
            nums.len() == nums_in.len(),
            forall|k: int| 0 <= k < j as int ==> ci[k] == change_indices_in[k],
            forall|k: int| 0 <= k < change_indices_in.len() ==> 1 <= #[trigger] change_indices_in[k] <= nums_in.len(),
        decreases change_indices_in.len() - j,
    {
        ci.push(change_indices_in[j]);
        j = j + 1;
    }

    (nums, ci, t_in)
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
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn gen_nums(rng: &mut Rng, n: usize, max_val: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.range_i32(0, max_val));
    }
    v
}

fn gen_change_indices(rng: &mut Rng, m: usize, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(m);
    for _ in 0..m {
        v.push(rng.range_i32(1, n as i32));
    }
    v
}

fn print_json(nums: &[i32], ci: &[i32], t: usize) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    print!("],\"change_indices\":[");
    for i in 0..ci.len() {
        if i > 0 { print!(","); }
        print!("{}", ci[i]);
    }
    println!("],\"t\":{}}}", t);
}

fn build_and_emit(rng: &mut Rng, nums: Vec<i32>, ci: Vec<i32>, t: usize) {
    // Clamp/validate
    if nums.is_empty() || nums.len() > 2000 { return; }
    if ci.is_empty() || ci.len() > 2000 { return; }
    if t < 1 || t > ci.len() { return; }
    for &x in &nums { if x < 0 || x > 1_000_000_000 { return; } }
    for &x in &ci { if x < 1 || x > nums.len() as i32 { return; } }
    let _ = rng;
    let (a, b, c) = generate_test_case(&nums, &ci, t);
    print_json(&a, &b, c);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);

    let total = 200usize;

    for tc in 0..total {
        let mode = tc % 10;
        match mode {
            0 => {
                // small random
                let n = rng.range_usize(1, 10);
                let m = rng.range_usize(1, 10);
                let nums = gen_nums(&mut rng, n, 5);
                let ci = gen_change_indices(&mut rng, m, n);
                let t = rng.range_usize(1, m);
                build_and_emit(&mut rng, nums, ci, t);
            }
            1 => {
                // all zeros - trivially markable when each index appears
                let n = rng.range_usize(1, 20);
                let m = rng.range_usize(n, 40);
                let nums = vec![0i32; n];
                let ci = gen_change_indices(&mut rng, m, n);
                let t = m;
                build_and_emit(&mut rng, nums, ci, t);
            }
            2 => {
                // missing index (Example 3 style)
                let n = rng.range_usize(2, 10);
                let m = rng.range_usize(1, 20);
                let nums = gen_nums(&mut rng, n, 3);
                let mut ci = Vec::with_capacity(m);
                for _ in 0..m {
                    // only indices 1..n (exclude n)
                    ci.push(rng.range_i32(1, (n - 1) as i32));
                }
                let t = rng.range_usize(1, m);
                build_and_emit(&mut rng, nums, ci, t);
            }
            3 => {
                // maximum sizes
                let n = 2000usize;
                let m = 2000usize;
                let nums = gen_nums(&mut rng, n, 1_000_000_000);
                let ci = gen_change_indices(&mut rng, m, n);
                let t = m;
                build_and_emit(&mut rng, nums, ci, t);
            }
            4 => {
                // large values with small n
                let n = rng.range_usize(1, 5);
                let m = rng.range_usize(1, 20);
                let nums = gen_nums(&mut rng, n, 1_000_000_000);
                let ci = gen_change_indices(&mut rng, m, n);
                let t = rng.range_usize(1, m);
                build_and_emit(&mut rng, nums, ci, t);
            }
            5 => {
                // Example 1
                let nums = vec![2, 2, 0];
                let ci = vec![2, 2, 2, 2, 3, 2, 2, 1];
                let t = rng.range_usize(1, 8);
                build_and_emit(&mut rng, nums, ci, t);
            }
            6 => {
                // Example 2
                let nums = vec![1, 3];
                let ci = vec![1, 1, 1, 2, 1, 1, 1];
                let t = rng.range_usize(1, 7);
                build_and_emit(&mut rng, nums, ci, t);
            }
            7 => {
                // n == 1
                let n = 1usize;
                let m = rng.range_usize(1, 50);
                let nums = gen_nums(&mut rng, n, 20);
                let ci = vec![1i32; m];
                let t = rng.range_usize(1, m);
                build_and_emit(&mut rng, nums, ci, t);
            }
            8 => {
                // t = 1
                let n = rng.range_usize(1, 30);
                let m = rng.range_usize(1, 100);
                let nums = gen_nums(&mut rng, n, 10);
                let ci = gen_change_indices(&mut rng, m, n);
                build_and_emit(&mut rng, nums, ci, 1);
            }
            _ => {
                // m >> n with repetitions
                let n = rng.range_usize(2, 20);
                let m = rng.range_usize(50, 500);
                let nums = gen_nums(&mut rng, n, 100);
                let ci = gen_change_indices(&mut rng, m, n);
                let t = rng.range_usize(1, m);
                build_and_emit(&mut rng, nums, ci, t);
            }
        }
    }
}