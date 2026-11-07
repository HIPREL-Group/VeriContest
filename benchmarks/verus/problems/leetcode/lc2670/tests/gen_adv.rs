use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    left: usize,
    right: usize,
    vals: &Vec<i32>,
) -> (result: (Vec<i32>, usize, usize))
    requires
        1 <= n <= 50,
        left <= right <= n,
        vals.len() == n,
        forall|i: int| 0 <= i < vals.len() ==> 1 <= #[trigger] vals[i] <= 50,
    ensures
        ({
            let (nums, l, r) = result;
            &&& 1 <= nums.len() <= 50
            &&& nums.len() == n
            &&& l == left
            &&& r == right
            &&& l <= r <= nums.len()
            &&& forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 50
        }),
{
    let mut nums: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            0 <= k <= n,
            n == vals.len(),
            nums.len() == k,
            forall|i: int| 0 <= i < k as int ==> 1 <= #[trigger] nums[i] <= 50,
            forall|i: int| 0 <= i < k as int ==> nums[i] == vals[i],
            forall|i: int| 0 <= i < vals.len() ==> 1 <= #[trigger] vals[i] <= 50,
        decreases n - k,
    {
        nums.push(vals[k]);
        k = k + 1;
    }
    (nums, left, right)
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
        if lo >= hi {
            return lo;
        }
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        if lo >= hi {
            return lo;
        }
        let span = (hi - lo + 1) as u64;
        lo + ((self.next_u64() % span) as i32)
    }
}

fn build_vals(rng: &mut Rng, n: usize, mode: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // all same
            let x = rng.gen_range_i32(1, 50);
            for _ in 0..n {
                v.push(x);
            }
        }
        1 => {
            // all distinct increasing (mod 50)
            for i in 0..n {
                v.push(((i % 50) as i32) + 1);
            }
        }
        2 => {
            // alternating two values
            let a = rng.gen_range_i32(1, 50);
            let mut b = rng.gen_range_i32(1, 50);
            if b == a {
                b = if a == 50 { 1 } else { a + 1 };
            }
            for i in 0..n {
                v.push(if i % 2 == 0 { a } else { b });
            }
        }
        3 => {
            // all 1s
            for _ in 0..n {
                v.push(1);
            }
        }
        4 => {
            // all 50s
            for _ in 0..n {
                v.push(50);
            }
        }
        5 => {
            // ascending
            for i in 0..n {
                let x = ((i as i32) % 50) + 1;
                v.push(x);
            }
        }
        6 => {
            // descending
            for i in 0..n {
                let x = 50 - ((i as i32) % 50);
                v.push(x);
            }
        }
        7 => {
            // only one distinct then another
            let a = rng.gen_range_i32(1, 50);
            let mut b = rng.gen_range_i32(1, 50);
            if b == a {
                b = if a == 50 { 1 } else { a + 1 };
            }
            let split = n / 2;
            for i in 0..n {
                v.push(if i < split { a } else { b });
            }
        }
        8 => {
            // small range repeats
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 3));
            }
        }
        _ => {
            // fully random
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 50));
            }
        }
    }
    v
}

fn print_json(nums: &[i32], left: usize, right: usize) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", nums[i]);
    }
    println!("],\"left\":{},\"right\":{}}}", left, right);
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
        let mode = t % 10;
        let n = match t % 7 {
            0 => 1,
            1 => 2,
            2 => 50,
            3 => 49,
            4 => 3,
            5 => rng.gen_range_usize(1, 50),
            _ => rng.gen_range_usize(1, 50),
        };

        let vals = build_vals(&mut rng, n, mode);

        // choose left/right: various edge cases
        let (left, right) = match t % 6 {
            0 => (0usize, n),
            1 => (0usize, 0usize),
            2 => (n, n),
            3 => {
                if n >= 2 { (1usize, n - 1) } else { (0, n) }
            }
            4 => {
                let l = rng.gen_range_usize(0, n);
                let r = rng.gen_range_usize(l, n);
                (l, r)
            }
            _ => {
                let l = rng.gen_range_usize(0, n);
                (l, l)
            }
        };

        let (nums, l, r) = generate_test_case(n, left, right, &vals);
        print_json(&nums, l, r);
    }
}