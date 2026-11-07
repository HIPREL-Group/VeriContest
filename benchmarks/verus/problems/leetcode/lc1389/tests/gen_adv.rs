use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    nums_src: &Vec<i32>,
    index_src: &Vec<i32>,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= n <= 100,
        nums_src.len() == n,
        index_src.len() == n,
        forall |i: int| 0 <= i < n ==> 0 <= #[trigger] nums_src[i] <= 100,
        forall |i: int| 0 <= i < n ==> 0 <= #[trigger] index_src[i] <= i,
    ensures
        1 <= result.0.len() <= 100,
        result.0.len() == result.1.len(),
        forall |i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 100,
        forall |i: int| 0 <= i < result.1.len() ==> 0 <= #[trigger] result.1[i] <= i,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut index: Vec<i32> = Vec::new();
    let mut k: usize = 0;

    while k < n
        invariant
            0 <= k <= n,
            1 <= n <= 100,
            nums.len() == k,
            index.len() == k,
            nums_src.len() == n,
            index_src.len() == n,
            forall |i: int| 0 <= i < n ==> 0 <= #[trigger] nums_src[i] <= 100,
            forall |i: int| 0 <= i < n ==> 0 <= #[trigger] index_src[i] <= i,
            forall |i: int| 0 <= i < k as int ==> nums[i] == nums_src[i],
            forall |i: int| 0 <= i < k as int ==> index[i] == index_src[i],
            forall |i: int| 0 <= i < k as int ==> 0 <= #[trigger] nums[i] <= 100,
            forall |i: int| 0 <= i < k as int ==> 0 <= #[trigger] index[i] <= i,
        decreases n - k,
    {
        nums.push(nums_src[k]);
        index.push(index_src[k]);
        k = k + 1;
    }

    (nums, index)
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
        if lo >= hi { return lo; }
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
}

fn build_index(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        v.push(rng.gen_range_usize(0, i) as i32);
    }
    v
}

fn build_nums_random(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_usize(0, 100) as i32);
    }
    v
}

fn mode_case(rng: &mut Rng, mode: usize, t: usize) -> (usize, Vec<i32>, Vec<i32>) {
    match mode {
        0 => {
            // n = 1
            let nums = vec![rng.gen_range_usize(0, 100) as i32];
            let index = vec![0i32];
            (1, nums, index)
        }
        1 => {
            // n = 100, all index 0 (always insert at front)
            let n = 100;
            let mut idx = Vec::with_capacity(n);
            for _ in 0..n { idx.push(0i32); }
            (n, build_nums_random(rng, n), idx)
        }
        2 => {
            // n = 100, index[i] = i (always append)
            let n = 100;
            let mut idx = Vec::with_capacity(n);
            for i in 0..n { idx.push(i as i32); }
            (n, build_nums_random(rng, n), idx)
        }
        3 => {
            // n = 100, index[i] = i/2
            let n = 100;
            let mut idx = Vec::with_capacity(n);
            for i in 0..n { idx.push((i / 2) as i32); }
            (n, build_nums_random(rng, n), idx)
        }
        4 => {
            // small n like the examples
            let n = 5;
            let nums = vec![0,1,2,3,4];
            let index = vec![0,1,2,2,1];
            (n, nums, index)
        }
        5 => {
            // n = 100, values all 0
            let n = 100;
            let nums: Vec<i32> = (0..n).map(|_| 0i32).collect();
            (n, nums, build_index(rng, n))
        }
        6 => {
            // n = 100, values all 100
            let n = 100;
            let nums: Vec<i32> = (0..n).map(|_| 100i32).collect();
            (n, nums, build_index(rng, n))
        }
        7 => {
            // index[i] = i (append)
            let n = rng.gen_range_usize(1, 100);
            let mut idx = Vec::with_capacity(n);
            for i in 0..n { idx.push(i as i32); }
            (n, build_nums_random(rng, n), idx)
        }
        8 => {
            // alternating pattern
            let n = rng.gen_range_usize(2, 100);
            let mut idx = Vec::with_capacity(n);
            for i in 0..n {
                if i % 2 == 0 { idx.push(0); } else { idx.push(i as i32); }
            }
            (n, build_nums_random(rng, n), idx)
        }
        9 => {
            // random size, fully random
            let n = rng.gen_range_usize(1, 100);
            let nums = build_nums_random(rng, n);
            let idx = build_index(rng, n);
            (n, nums, idx)
        }
        _ => {
            let n = rng.gen_range_usize(1, 100);
            let mut nums = Vec::with_capacity(n);
            for i in 0..n { nums.push((i * 7 + t) as i32 % 101); }
            let idx = build_index(rng, n);
            (n, nums, idx)
        }
    }
}

fn print_json(nums: &[i32], index: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    print!("],\"index\":[");
    for i in 0..index.len() {
        if i > 0 { print!(","); }
        print!("{}", index[i]);
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
        let (n, nums_src, index_src) = mode_case(&mut rng, mode, t);
        // Sanity clamp (should already be valid)
        if n < 1 || n > 100 || nums_src.len() != n || index_src.len() != n { continue; }
        let mut ok = true;
        for i in 0..n {
            if nums_src[i] < 0 || nums_src[i] > 100 { ok = false; break; }
            if index_src[i] < 0 || index_src[i] > i as i32 { ok = false; break; }
        }
        if !ok { continue; }

        let (nums, index) = generate_test_case(n, &nums_src, &index_src);
        print_json(&nums, &index);
    }
}