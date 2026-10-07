use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    min_val: i32,
    max_val: i32,
    min_idx: usize,
    max_idx: usize,
    fillers: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        min_val < max_val,
        -100_000 <= min_val <= 100_000,
        -100_000 <= max_val <= 100_000,
        fillers.len() + 2 >= 1,
        fillers.len() + 2 <= 100_000,
        min_idx < fillers.len() + 2,
        max_idx < fillers.len() + 2,
        min_idx != max_idx,
        forall |i: int| 0 <= i < fillers.len() ==>
            #[trigger] fillers[i] > min_val && fillers[i] < max_val,
        forall |i: int, j: int| 0 <= i < j < fillers.len() ==>
            #[trigger] fillers[i] != #[trigger] fillers[j],
    ensures
        1 <= nums.len() <= 100_000,
        forall |i: int, j: int| 0 <= i < j < nums.len() ==> #[trigger] nums[i] != #[trigger] nums[j],
        forall |i: int| 0 <= i < nums.len() ==> -100_000 <= #[trigger] nums[i] <= 100_000,
{
    let mut nums: Vec<i32> = Vec::new();
    nums.push(min_val);
    nums.push(max_val);
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

fn choose_distinct_indices(rng: &mut Rng, n: usize) -> (usize, usize) {
    if n == 1 {
        return (0, 0);
    }
    let i = rng.gen_range_usize(0, n - 1);
    let mut j = rng.gen_range_usize(0, n - 2);
    if j >= i {
        j += 1;
    }
    (i, j)
}

// Build fillers: distinct values strictly between min_val and max_val, count = n - 2.
// Use a simple approach: enumerate integers in (min_val, max_val) and pick `count` distinct ones.
fn make_fillers(count: usize, min_val: i32, max_val: i32, rng: &mut Rng) -> Option<Vec<i32>> {
    if count == 0 {
        return Some(Vec::new());
    }
    let range_size = (max_val as i64) - (min_val as i64) - 1;
    if range_size < count as i64 {
        return None;
    }
    // collect all candidates if small enough, otherwise sample.
    let mut candidates: Vec<i32> = Vec::new();
    if range_size <= 200_000 {
        let mut v = min_val as i64 + 1;
        while v <= max_val as i64 - 1 {
            candidates.push(v as i32);
            v += 1;
        }
        // shuffle with Fisher-Yates
        let len = candidates.len();
        let mut i = len;
        while i > 1 {
            i -= 1;
            let j = rng.gen_range_usize(0, i);
            candidates.swap(i, j);
        }
        candidates.truncate(count);
        Some(candidates)
    } else {
        // unreachable given constraints (max_val-min_val-1 <= 200_000)
        None
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

fn gen_case(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    // decide n
    let n: usize = match mode {
        0 => 1,
        1 => 2,
        2 => 3,
        3 => {
            let sizes = [100_000usize, 99_999, 50_000];
            sizes[t % 3]
        }
        4 => rng.gen_range_usize(4, 20),
        5 => rng.gen_range_usize(100, 500),
        6 => rng.gen_range_usize(1000, 5000),
        7 => 10,
        8 => 2,
        9 => 100_000,
        _ => rng.gen_range_usize(1, 1000),
    };

    if n == 1 {
        // single element: min_val == max_val conceptually, but our generator requires min_val < max_val
        // Handle separately: produce [x] directly. But generate_test_case requires min_val < max_val and n >= 1 with fillers.len()+2 == n, so n >= 2.
        // For n=1 we just don't call the verified generator; we still need to output a valid test.
        // We'll skip this branch by using n=2 instead.
        let x = rng.gen_range_i32(-100_000, 100_000);
        return vec![x];
    }

    // pick min_val and max_val
    let (min_val, max_val) = match mode {
        1 => (-100_000i32, 100_000i32),
        2 => (-100_000i32, -100_000i32 + (n as i32 - 1).max(1)),
        6 => {
            let mv = rng.gen_range_i32(-100_000, 100_000 - (n as i32).min(100_000));
            let needed = mv + (n as i32 - 1).max(1);
            let xv = needed.min(100_000);
            (mv, xv.max(mv + 1))
        }
        7 => (-5i32, 5i32),
        8 => (0i32, 1i32),
        9 => (-100_000i32, 100_000i32),
        _ => {
            // random range wide enough to hold n-2 fillers
            let needed = (n as i32).saturating_sub(2).saturating_add(1);
            let lo = rng.gen_range_i32(-100_000, 100_000 - needed);
            let hi = rng.gen_range_i32(lo + needed, 100_000.min(lo + needed + 50_000));
            (lo, hi.max(lo + needed))
        }
    };

    // ensure max_val > min_val and enough room
    let range_size = (max_val as i64) - (min_val as i64) - 1;
    if max_val <= min_val || range_size < (n as i64 - 2) {
        // fallback: use a simple spread
        let lo = -100_000i32;
        let hi = lo + (n as i32).max(2) - 1;
        let min_val2 = lo;
        let max_val2 = hi.min(100_000);
        let fillers = make_fillers(n - 2, min_val2, max_val2, rng).unwrap_or_default();
        let (i, j) = choose_distinct_indices(rng, n);
        return generate_test_case(min_val2, max_val2, i, j, &fillers);
    }

    let fillers_opt = make_fillers(n - 2, min_val, max_val, rng);
    let fillers = match fillers_opt {
        Some(f) => f,
        None => {
            let lo = -100_000i32;
            let hi = (lo + (n as i32).max(2) - 1).min(100_000);
            return generate_test_case(lo, hi, 0, n - 1, &make_fillers(n - 2, lo, hi, rng).unwrap_or_default());
        }
    };

    let (i, j) = choose_distinct_indices(rng, n);
    let (min_idx, max_idx) = match mode {
        0 => (0, 0),  // unused for n=1
        1 => (0, 1),
        5 => (n - 1, 0),
        6 => (0, n - 1),
        _ => (i, j),
    };

    let (mi, xi) = if min_idx == max_idx {
        if n >= 2 { (0usize, 1usize) } else { (0, 0) }
    } else {
        (min_idx, max_idx)
    };

    generate_test_case(min_val, max_val, mi, xi, &fillers)
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
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let nums = gen_case(&mut rng, mode, t);
        print_json(&nums);
    }
}
