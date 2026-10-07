use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    offset: i32,
) -> (nums: Vec<i32>)
    requires
        1 <= n <= 100,
        1 <= offset,
        offset as int + n as int - 1 <= 100,
    ensures
        1 <= nums.len() <= 100,
        nums.len() == n,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] != nums[j],
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            1 <= n <= 100,
            1 <= offset,
            offset as int + n as int - 1 <= 100,
            nums.len() == i,
            forall|k: int| 0 <= k < i as int ==> #[trigger] nums[k] == offset as int + k,
            forall|k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 100,
        decreases n - i,
    {
        let v: i32 = offset + (i as i32);
        nums.push(v);
        i = i + 1;
    }

    proof {
        assert forall|a: int, b: int| 0 <= a < b < nums.len() implies nums[a] != nums[b] by {
            assert(nums[a] == offset as int + a);
            assert(nums[b] == offset as int + b);
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

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
}

fn shuffle(rng: &mut Rng, v: &mut Vec<i32>) {
    let n = v.len();
    if n <= 1 { return; }
    for i in (1..n).rev() {
        let j = rng.gen_range_usize(0, i);
        v.swap(i, j);
    }
}

fn pick_params(rng: &mut Rng, mode: usize) -> (usize, i32) {
    match mode {
        0 => (1, rng.gen_range_usize(1, 100) as i32),
        1 => (2, rng.gen_range_usize(1, 99) as i32),
        2 => (3, rng.gen_range_usize(1, 98) as i32),
        3 => (100, 1),
        4 => (99, rng.gen_range_usize(1, 2) as i32),
        5 => {
            let n = rng.gen_range_usize(3, 10);
            let offset_max = 100 - n + 1;
            let offset = rng.gen_range_usize(1, offset_max) as i32;
            (n, offset)
        }
        6 => {
            let n = rng.gen_range_usize(50, 100);
            let offset_max = 100 - n + 1;
            let offset = rng.gen_range_usize(1, offset_max) as i32;
            (n, offset)
        }
        7 => (3, 1),
        8 => (3, 98),
        9 => {
            let n = rng.gen_range_usize(1, 100);
            let offset_max = 100 - n + 1;
            let offset = rng.gen_range_usize(1, offset_max) as i32;
            (n, offset)
        }
        _ => {
            let n = rng.gen_range_usize(2, 100);
            let offset_max = 100 - n + 1;
            let offset = rng.gen_range_usize(1, offset_max) as i32;
            (n, offset)
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
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let (n, offset) = pick_params(&mut rng, mode);
        let mut nums = generate_test_case(n, offset);
        // Optionally shuffle for variety (still satisfies preconditions)
        if t % 2 == 0 {
            shuffle(&mut rng, &mut nums);
        }
        print_json(&nums);
    }
}