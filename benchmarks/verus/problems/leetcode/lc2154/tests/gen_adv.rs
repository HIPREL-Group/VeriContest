use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    fillers: &Vec<i32>,
    original: i32,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= fillers.len() <= 1000,
        1 <= original <= 1000,
        forall |i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 1000,
    ensures
        ({
            let (nums, orig) = result;
            &&& 1 <= nums.len() <= 1000
            &&& forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000
            &&& 1 <= orig <= 1000
            &&& orig == original
        }),
{
    let mut nums: Vec<i32> = Vec::new();
    let n = fillers.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == fillers.len(),
            0 <= i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < fillers.len() ==> 1 <= #[trigger] fillers[k] <= 1000,
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 1000,
        decreases n - i,
    {
        nums.push(fillers[i]);
        i = i + 1;
    }
    (nums, original)
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
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_fillers(rng: &mut Rng, n: usize, mode: usize, original: i32) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // chain of powers starting from original
            let mut cur: i32 = original;
            let mut idx = 0;
            while idx < n {
                if cur <= 1000 {
                    v.push(cur);
                    if cur as i64 * 2 <= 1000 {
                        cur = cur * 2;
                    } else {
                        // fill rest with random values not equal to any power chain
                        let fill = rng.gen_range_i32(1, 1000);
                        v.push(fill);
                    }
                } else {
                    v.push(rng.gen_range_i32(1, 1000));
                }
                idx = v.len();
                if idx >= n { break; }
            }
            while v.len() > n {
                v.pop();
            }
        }
        1 => {
            // all same as original
            for _ in 0..n {
                v.push(original);
            }
        }
        2 => {
            // no matches at all (all > 1000 impossible, so pick values not in chain)
            let mut forbidden: Vec<i32> = Vec::new();
            let mut c = original as i64;
            while c <= 1000 {
                forbidden.push(c as i32);
                c *= 2;
            }
            for _ in 0..n {
                let mut x = rng.gen_range_i32(1, 1000);
                let mut tries = 0;
                while forbidden.contains(&x) && tries < 20 {
                    x = rng.gen_range_i32(1, 1000);
                    tries += 1;
                }
                if forbidden.contains(&x) {
                    x = if original == 1 { 3 } else { 1 };
                    // ensure x not in chain
                    if forbidden.contains(&x) {
                        x = 999;
                        while forbidden.contains(&x) { x -= 1; if x < 1 { x = 1; break; } }
                    }
                }
                v.push(x);
            }
        }
        3 => {
            // only partial chain
            let mut cur: i32 = original;
            let limit = rng.gen_range_usize(1, 3);
            let mut steps = 0;
            while v.len() < n {
                if steps < limit && cur <= 1000 {
                    v.push(cur);
                    if cur as i64 * 2 <= 1000 {
                        cur *= 2;
                    }
                    steps += 1;
                } else {
                    v.push(rng.gen_range_i32(1, 1000));
                }
            }
        }
        4 => {
            // original = 1 case
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 1000));
            }
        }
        5 => {
            // duplicates of powers
            let mut cur = original;
            while cur <= 1000 && v.len() < n {
                v.push(cur);
                if v.len() < n { v.push(cur); }
                if cur as i64 * 2 <= 1000 { cur *= 2; } else { break; }
            }
            while v.len() < n {
                v.push(rng.gen_range_i32(1, 1000));
            }
        }
        6 => {
            // reverse order powers
            let mut powers: Vec<i32> = Vec::new();
            let mut c = original as i64;
            while c <= 1000 {
                powers.push(c as i32);
                c *= 2;
            }
            for p in powers.iter().rev() {
                if v.len() >= n { break; }
                v.push(*p);
            }
            while v.len() < n {
                v.push(rng.gen_range_i32(1, 1000));
            }
        }
        7 => {
            // all 1000
            for _ in 0..n {
                v.push(1000);
            }
        }
        8 => {
            // contains 2*original but not original
            let doubled = if (original as i64 * 2) <= 1000 { original * 2 } else { original };
            for _ in 0..n {
                v.push(doubled);
            }
        }
        _ => {
            // random
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 1000));
            }
        }
    }
    // ensure length = n
    while v.len() < n {
        v.push(1);
    }
    while v.len() > n {
        v.pop();
    }
    // sanity: all in [1,1000]
    for i in 0..v.len() {
        if v[i] < 1 { v[i] = 1; }
        if v[i] > 1000 { v[i] = 1000; }
    }
    v
}

fn print_json(nums: &[i32], original: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("],\"original\":{}}}", original);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => rng.gen_range_usize(1, 20),
            1 => 1000,
            2 => rng.gen_range_usize(1, 50),
            3 => rng.gen_range_usize(5, 100),
            4 => rng.gen_range_usize(1, 1000),
            5 => rng.gen_range_usize(2, 20),
            6 => rng.gen_range_usize(3, 30),
            7 => rng.gen_range_usize(1, 10),
            8 => rng.gen_range_usize(1, 10),
            _ => rng.gen_range_usize(1, 1000),
        };

        let original = match mode {
            4 => 1,
            7 => 1000,
            1 => rng.gen_range_i32(1, 1000),
            _ => rng.gen_range_i32(1, 500),
        };

        let fillers = build_fillers(&mut rng, n, mode, original);
        let (nums, orig) = generate_test_case(&fillers, original);
        print_json(&nums, orig);
    }
}