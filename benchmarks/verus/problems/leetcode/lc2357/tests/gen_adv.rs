use vstd::prelude::*;

verus! {

pub fn generate_test_case(len: usize, fillers: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= len <= 100,
        fillers.len() == len,
        forall |i: int| 0 <= i < fillers.len() ==> 0 <= #[trigger] fillers[i] <= 100,
    ensures
        1 <= nums.len() <= 100,
        forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 100,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            len == fillers.len(),
            1 <= len <= 100,
            nums.len() == i,
            forall |k: int| 0 <= k < fillers.len() ==> 0 <= #[trigger] fillers[k] <= 100,
            forall |k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] <= 100,
            forall |k: int| 0 <= k < nums.len() ==> nums[k] == fillers[k],
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
        let span = (hi - lo + 1) as u64;
        lo + ((self.next_u64() % span) as i32)
    }
}

fn make_fillers_random(rng: &mut Rng, n: usize, lo: i32, hi: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i32(lo, hi));
    }
    v
}

fn make_all(n: usize, val: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(val);
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

fn build_and_print(n: usize, fillers: Vec<i32>) {
    let nums = generate_test_case(n, &fillers);
    print_json(&nums);
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
        let mode = t % 11;
        let (n, fillers) = match mode {
            0 => {
                // single zero
                (1, vec![0i32])
            }
            1 => {
                // all zeros
                let n = rng.gen_range_usize(1, 100);
                (n, make_all(n, 0))
            }
            2 => {
                // all same non-zero value
                let n = rng.gen_range_usize(1, 100);
                let v = rng.gen_range_i32(1, 100);
                (n, make_all(n, v))
            }
            3 => {
                // max length random 0..100
                let n = 100;
                (n, make_fillers_random(&mut rng, n, 0, 100))
            }
            4 => {
                // min length 1, random
                let v = rng.gen_range_i32(0, 100);
                (1, vec![v])
            }
            5 => {
                // two distinct values
                let n = rng.gen_range_usize(2, 100);
                let a = rng.gen_range_i32(1, 100);
                let mut b = rng.gen_range_i32(1, 100);
                if b == a { b = if a < 100 { a + 1 } else { a - 1 }; }
                let mut v = Vec::with_capacity(n);
                for i in 0..n {
                    v.push(if i % 2 == 0 { a } else { b });
                }
                (n, v)
            }
            6 => {
                // sequence 1..=n (capped at 100)
                let n = rng.gen_range_usize(1, 100);
                let mut v = Vec::with_capacity(n);
                for i in 0..n {
                    v.push(((i as i32) % 100) + 1);
                }
                (n, v)
            }
            7 => {
                // all max value 100
                let n = rng.gen_range_usize(1, 100);
                (n, make_all(n, 100))
            }
            8 => {
                // mostly zeros with one non-zero
                let n = rng.gen_range_usize(1, 100);
                let mut v = make_all(n, 0);
                let idx = rng.gen_range_usize(0, n - 1);
                v[idx] = rng.gen_range_i32(1, 100);
                (n, v)
            }
            9 => {
                // small range values 0..5
                let n = rng.gen_range_usize(1, 100);
                (n, make_fillers_random(&mut rng, n, 0, 5))
            }
            _ => {
                // general random
                let n = rng.gen_range_usize(1, 100);
                (n, make_fillers_random(&mut rng, n, 0, 100))
            }
        };
        build_and_print(n, fillers);
    }
}