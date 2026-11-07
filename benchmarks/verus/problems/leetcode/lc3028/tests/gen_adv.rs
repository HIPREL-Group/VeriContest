use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 100,
        forall |i: int| 0 <= i < values.len() ==> -10 <= #[trigger] values[i] <= 10,
        forall |i: int| 0 <= i < values.len() ==> #[trigger] values[i] != 0,
    ensures
        1 <= nums.len() <= 100,
        forall |i: int| 0 <= i < nums.len() ==> -10 <= #[trigger] nums[i] <= 10,
        forall |i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] != 0,
{
    let mut nums: Vec<i32> = Vec::new();
    let n = values.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            nums.len() == i,
            1 <= values.len() <= 100,
            forall |k: int| 0 <= k < values.len() ==> -10 <= #[trigger] values[k] <= 10,
            forall |k: int| 0 <= k < values.len() ==> #[trigger] values[k] != 0,
            forall |k: int| 0 <= k < i as int ==> #[trigger] nums[k] == values[k],
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
        Self { state: seed.wrapping_add(1) }
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
    fn gen_nonzero_i32(&mut self) -> i32 {
        loop {
            let v = (self.next_u64() % 21) as i32 - 10;
            if v != 0 {
                return v;
            }
        }
    }
}

fn make_random(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_nonzero_i32());
    }
    v
}

fn make_all_ones(n: usize) -> Vec<i32> {
    (0..n).map(|_| 1i32).collect()
}

fn make_alternating(n: usize) -> Vec<i32> {
    (0..n).map(|i| if i % 2 == 0 { 1i32 } else { -1i32 }).collect()
}

fn make_sum_zero(rng: &mut Rng, n: usize) -> Vec<i32> {
    // fill n-1 random, pick last so sum across windows hits zero occasionally
    let mut v = Vec::with_capacity(n);
    let mut s: i32 = 0;
    for _ in 0..(n.saturating_sub(1)) {
        let x = rng.gen_nonzero_i32();
        v.push(x);
        s += x;
    }
    if n >= 1 {
        // last element makes total sum 0 if possible
        let last = if s == 0 { 1 } else { -s };
        let clamped = if last > 10 { 10 } else if last < -10 { -10 } else if last == 0 { 1 } else { last };
        v.push(clamped);
    }
    v
}

fn make_big_swings(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        let val = if i % 2 == 0 { 10 } else { -10 };
        let _ = rng.next_u64();
        v.push(val);
    }
    v
}

fn make_single(rng: &mut Rng) -> Vec<i32> {
    vec![rng.gen_nonzero_i32()]
}

fn make_pairs_cancel(n: usize) -> Vec<i32> {
    // pattern: 2, -2, 3, -3, ...
    let mut v = Vec::with_capacity(n);
    let mut x = 1;
    let mut up = true;
    for _ in 0..n {
        if up {
            v.push(x);
            up = false;
        } else {
            v.push(-x);
            up = true;
            x += 1;
            if x > 10 { x = 1; }
        }
    }
    v
}

fn make_all_positive(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        let x = (rng.next_u64() % 10) as i32 + 1;
        v.push(x);
    }
    v
}

fn make_all_negative(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        let x = -((rng.next_u64() % 10) as i32 + 1);
        v.push(x);
    }
    v
}

fn make_known_example1() -> Vec<i32> {
    vec![2, 3, -5]
}

fn make_known_example2() -> Vec<i32> {
    vec![3, 2, -3, -4]
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

    let total = 200usize;
    for t in 0..total {
        let mode = t % 10;
        let n = match mode {
            0 => 1,
            1 => 100,
            2 => rng.gen_range_usize(1, 100),
            3 => rng.gen_range_usize(2, 20),
            4 => rng.gen_range_usize(10, 50),
            5 => 100,
            6 => rng.gen_range_usize(1, 100),
            7 => rng.gen_range_usize(1, 100),
            8 => rng.gen_range_usize(1, 100),
            _ => rng.gen_range_usize(1, 100),
        };

        let values: Vec<i32> = match mode {
            0 => make_single(&mut rng),
            1 => make_all_ones(n),
            2 => make_alternating(n),
            3 => make_sum_zero(&mut rng, n),
            4 => make_big_swings(&mut rng, n),
            5 => make_pairs_cancel(n),
            6 => make_all_positive(&mut rng, n),
            7 => make_all_negative(&mut rng, n),
            8 => {
                if t % 20 == 0 { make_known_example1() }
                else if t % 20 == 10 { make_known_example2() }
                else { make_random(&mut rng, n) }
            }
            _ => make_random(&mut rng, n),
        };

        // validate and clamp defensively
        let mut safe: Vec<i32> = Vec::with_capacity(values.len());
        for &x in &values {
            let v = if x == 0 { 1 } else if x > 10 { 10 } else if x < -10 { -10 } else { x };
            safe.push(v);
        }
        if safe.is_empty() {
            safe.push(1);
        }
        if safe.len() > 100 {
            safe.truncate(100);
        }

        let nums = generate_test_case(&safe);
        print_json(&nums);
    }
}