use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n_val: i32,
    fillers: &Vec<i32>,
    left_val: i32,
    right_val: i32,
) -> (result: (Vec<i32>, i32, i32, i32))
    requires
        1 <= n_val <= 1000,
        fillers.len() == n_val as int,
        forall |i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 100,
        1 <= left_val <= right_val,
        right_val as int <= n_val as int * (n_val as int + 1) / 2,
    ensures
        result.1 == n_val,
        result.2 == left_val,
        result.3 == right_val,
        result.0@.len() == n_val as int,
        1 <= result.0@.len() <= 1000,
        forall |i: int| 0 <= i < result.0@.len() ==> 1 <= #[trigger] result.0@[i] <= 100,
        1 <= result.2 <= result.3,
        result.3 as int <= result.1 as int * (result.1 as int + 1) / 2,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    let target_len: usize = n_val as usize;

    while i < target_len
        invariant
            0 <= i <= target_len,
            target_len == n_val as int,
            nums.len() == i,
            fillers.len() == n_val as int,
            forall |k: int| 0 <= k < fillers.len() ==> 1 <= #[trigger] fillers[k] <= 100,
            forall |k: int| 0 <= k < nums.len() ==> nums[k] == fillers[k],
            forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100,
        decreases target_len - i,
    {
        nums.push(fillers[i]);
        i = i + 1;
    }

    (nums, n_val, left_val, right_val)
}

}

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

fn make_fillers(rng: &mut Rng, n: usize, mode: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    match mode {
        0 => {
            for _ in 0..n { v.push(rng.gen_range_i32(1, 100)); }
        }
        1 => {
            for _ in 0..n { v.push(1); }
        }
        2 => {
            for _ in 0..n { v.push(100); }
        }
        3 => {
            for i in 0..n { v.push(((i % 100) + 1) as i32); }
        }
        4 => {
            for i in 0..n { v.push((100 - (i % 100)) as i32); }
        }
        5 => {
            for i in 0..n {
                if i % 2 == 0 { v.push(1); } else { v.push(100); }
            }
        }
        6 => {
            for _ in 0..n { v.push(rng.gen_range_i32(1, 10)); }
        }
        7 => {
            for _ in 0..n { v.push(rng.gen_range_i32(90, 100)); }
        }
        8 => {
            let c = rng.gen_range_i32(1, 100);
            for _ in 0..n { v.push(c); }
        }
        _ => {
            for _ in 0..n { v.push(rng.gen_range_i32(1, 100)); }
        }
    }
    v
}

fn print_json(nums: &[i32], n: i32, left: i32, right: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("],\"n\":{},\"left\":{},\"right\":{}}}", n, left, right);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };

    let mut rng = Rng::new(seed);
    let modes = 9usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n: usize = match t % 11 {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => 4,
            4 => 5,
            5 => 10,
            6 => 50,
            7 => 100,
            8 => 500,
            9 => 1000,
            _ => rng.gen_range_usize(1, 100),
        };

        let fillers = make_fillers(&mut rng, n, mode);
        let total_sums: i64 = (n as i64) * (n as i64 + 1) / 2;

        // choose left, right in [1, total_sums]
        let (left, right) = {
            let mode_lr = t % 6;
            match mode_lr {
                0 => (1i64, total_sums),
                1 => (1i64, 1i64),
                2 => (total_sums, total_sums),
                3 => {
                    let l = rng.gen_range_usize(1, total_sums as usize) as i64;
                    (l, l)
                }
                4 => {
                    let l = 1i64;
                    let r = if total_sums >= 2 { 2 } else { 1 };
                    (l, r)
                }
                _ => {
                    let l = rng.gen_range_usize(1, total_sums as usize) as i64;
                    let r = rng.gen_range_usize(l as usize, total_sums as usize) as i64;
                    (l, r)
                }
            }
        };

        let n_i32 = n as i32;
        let left_i32 = left as i32;
        let right_i32 = right as i32;

        let (nums, nn, ll, rr) = generate_test_case(n_i32, &fillers, left_i32, right_i32);
        print_json(&nums, nn, ll, rr);
    }
}