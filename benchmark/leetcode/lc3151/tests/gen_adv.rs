use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 100,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100,
    ensures
        1 <= nums.len() <= 100,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            1 <= n <= 100,
            0 <= i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 100,
            forall |k: int| 0 <= k < i as int ==> #[trigger] nums[k] == values[k],
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 100,
        decreases n - i,
    {
        nums.push(values[i]);
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn make_alternating(n: usize, start_odd: bool) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        let is_odd = if start_odd { i % 2 == 0 } else { i % 2 == 1 };
        v.push(if is_odd { 1 } else { 2 });
    }
    v
}

fn make_all_same_parity(n: usize, odd: bool) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        let base = if odd { 1 } else { 2 };
        v.push(base + 2 * ((i % 50) as i32));
    }
    v
}

fn make_random(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i32(1, 100));
    }
    v
}

fn make_random_alternating(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    let mut parity = rng.gen_range_usize(0, 1);
    for _ in 0..n {
        let val = if parity == 0 {
            2 * rng.gen_range_i32(1, 50)
        } else {
            2 * rng.gen_range_i32(0, 49) + 1
        };
        v.push(val);
        parity = 1 - parity;
    }
    v
}

fn make_almost_alternating(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = make_random_alternating(rng, n);
    if n >= 2 {
        let idx = rng.gen_range_usize(0, n - 2);
        // Force v[idx] and v[idx+1] to same parity
        if v[idx] % 2 == 0 {
            v[idx + 1] = 2 * rng.gen_range_i32(1, 50);
        } else {
            v[idx + 1] = 2 * rng.gen_range_i32(0, 49) + 1;
        }
    }
    v
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
        let n = match mode {
            0 => 1,
            1 => 2,
            2 => 100,
            3 => rng.gen_range_usize(1, 100),
            4 => rng.gen_range_usize(2, 10),
            5 => rng.gen_range_usize(50, 100),
            _ => rng.gen_range_usize(1, 100),
        };

        let values = match mode {
            0 => vec![rng.gen_range_i32(1, 100)],
            1 => make_alternating(n, true),
            2 => make_alternating(n, false),
            3 => make_all_same_parity(n, true),
            4 => make_all_same_parity(n, false),
            5 => make_random(&mut rng, n),
            6 => make_random_alternating(&mut rng, n),
            7 => make_almost_alternating(&mut rng, n),
            8 => {
                // boundary values
                let mut v = Vec::with_capacity(n);
                for i in 0..n {
                    v.push(if i % 2 == 0 { 1 } else { 100 });
                }
                v
            }
            9 => {
                let mut v = Vec::with_capacity(n);
                for i in 0..n {
                    v.push(if i % 2 == 0 { 100 } else { 99 });
                }
                v
            }
            _ => make_random(&mut rng, n),
        };

        // Clamp to constraints
        let clamped: Vec<i32> = values.iter().map(|&x| {
            let mut y = x;
            if y < 1 { y = 1; }
            if y > 100 { y = 100; }
            y
        }).collect();

        let nums = generate_test_case(&clamped);
        print_json(&nums);
    }
}