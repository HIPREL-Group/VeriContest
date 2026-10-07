use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    one_idx: usize,
    bits: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= n <= 100000,
        bits.len() == n,
        one_idx < n,
        forall|i: int| 0 <= i < bits.len() ==> (#[trigger] bits[i]) == 0 || bits[i] == 1,
    ensures
        1 <= nums.len() <= 100000,
        forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] == 0 || nums[i] == 1,
        exists|i: int| 0 <= i < nums.len() && nums[i] == 1,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut pos: usize = 0;

    while pos < n
        invariant
            0 <= pos <= n,
            nums.len() == pos,
            1 <= n <= 100000,
            bits.len() == n,
            one_idx < n,
            forall|i: int| 0 <= i < bits.len() ==> (#[trigger] bits[i]) == 0 || bits[i] == 1,
            forall|k: int| 0 <= k < pos as int && k != one_idx as int ==>
                #[trigger] nums[k] == bits[k],
            forall|k: int| 0 <= k < pos as int && k == one_idx as int ==>
                #[trigger] nums[k] == 1,
            forall|k: int| 0 <= k < pos as int ==> #[trigger] nums[k] == 0 || nums[k] == 1,
        decreases n - pos,
    {
        if pos == one_idx {
            nums.push(1);
        } else {
            nums.push(bits[pos]);
        }
        pos = pos + 1;
    }

    proof {
        assert(nums[one_idx as int] == 1);
        assert(exists|i: int| 0 <= i < nums.len() && nums[i] == 1) by {
            assert(0 <= one_idx < nums.len() && nums[one_idx as int] == 1);
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
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_bit(&mut self) -> i32 {
        (self.next_u64() & 1) as i32
    }
}

fn make_bits_random(rng: &mut Rng, n: usize) -> (Vec<i32>, usize) {
    let mut bits = Vec::with_capacity(n);
    let mut has_one = false;
    for _ in 0..n {
        let b = rng.gen_bit();
        if b == 1 { has_one = true; }
        bits.push(b);
    }
    let one_idx = if has_one {
        // find some one
        let mut idx = 0usize;
        for i in 0..n {
            if bits[i] == 1 { idx = i; break; }
        }
        idx
    } else {
        let idx = rng.gen_range_usize(0, n - 1);
        bits[idx] = 1;
        idx
    };
    (bits, one_idx)
}

fn make_bits_all_ones(n: usize) -> (Vec<i32>, usize) {
    let mut bits = Vec::with_capacity(n);
    for _ in 0..n { bits.push(1); }
    (bits, 0)
}

fn make_bits_single_one(n: usize, pos: usize) -> (Vec<i32>, usize) {
    let mut bits = Vec::with_capacity(n);
    for i in 0..n {
        bits.push(if i == pos { 1 } else { 0 });
    }
    (bits, pos)
}

fn make_bits_grouped(n: usize, start: usize, count: usize) -> (Vec<i32>, usize) {
    let mut bits = Vec::with_capacity(n);
    for i in 0..n { bits.push(0); }
    let c = if count == 0 { 1 } else { count };
    let c = if c > n { n } else { c };
    for k in 0..c {
        bits[(start + k) % n] = 1;
    }
    (bits, start % n)
}

fn make_bits_alternating(n: usize) -> (Vec<i32>, usize) {
    let mut bits = Vec::with_capacity(n);
    let mut one_idx = 0usize;
    let mut found = false;
    for i in 0..n {
        let b = if i % 2 == 0 { 1 } else { 0 };
        if b == 1 && !found { one_idx = i; found = true; }
        bits.push(b);
    }
    if !found {
        bits[0] = 1;
        one_idx = 0;
    }
    (bits, one_idx)
}

fn make_bits_split(n: usize) -> (Vec<i32>, usize) {
    // ones at start and end, zeros in middle (tests circular)
    let mut bits = Vec::with_capacity(n);
    for i in 0..n { bits.push(0); }
    let q = n / 4;
    let q = if q == 0 { 1 } else { q };
    for i in 0..q { bits[i] = 1; }
    for i in 0..q { bits[n - 1 - i] = 1; }
    (bits, 0)
}

fn make_bits_two_groups(n: usize, rng: &mut Rng) -> (Vec<i32>, usize) {
    let mut bits = Vec::with_capacity(n);
    for i in 0..n { bits.push(0); }
    let a_start = rng.gen_range_usize(0, n - 1);
    let a_len = rng.gen_range_usize(1, (n / 4).max(1));
    let b_start = rng.gen_range_usize(0, n - 1);
    let b_len = rng.gen_range_usize(1, (n / 4).max(1));
    for k in 0..a_len { bits[(a_start + k) % n] = 1; }
    for k in 0..b_len { bits[(b_start + k) % n] = 1; }
    (bits, a_start % n)
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
    } else { 1 };

    let mut rng = Rng::new(seed);
    let total = 200usize;
    let modes = 10usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => 1 + (t % 10),
            1 => 2 + (t % 20),
            2 => 100000,
            3 => 1,
            4 => 50 + (t % 50),
            5 => 1000 + (t % 500),
            6 => 10000,
            7 => 5 + (t % 15),
            8 => 500,
            _ => 200 + (t % 300),
        };
        let n = if n == 0 { 1 } else { n };
        let n = if n > 100000 { 100000 } else { n };

        let (bits, one_idx) = match mode {
            0 => make_bits_random(&mut rng, n),
            1 => make_bits_all_ones(n),
            2 => {
                let pos = rng.gen_range_usize(0, n - 1);
                make_bits_single_one(n, pos)
            }
            3 => {
                let start = rng.gen_range_usize(0, n - 1);
                let count = rng.gen_range_usize(1, n);
                make_bits_grouped(n, start, count)
            }
            4 => make_bits_alternating(n),
            5 => make_bits_split(n),
            6 => make_bits_two_groups(n, &mut rng),
            7 => make_bits_random(&mut rng, n),
            8 => {
                // mostly zeros with a few ones
                let mut bits = Vec::with_capacity(n);
                for _ in 0..n { bits.push(0); }
                let count = rng.gen_range_usize(1, (n / 10).max(1));
                let mut one_idx = 0usize;
                for k in 0..count {
                    let p = rng.gen_range_usize(0, n - 1);
                    bits[p] = 1;
                    if k == 0 { one_idx = p; }
                }
                (bits, one_idx)
            }
            _ => {
                // mostly ones with a few zeros
                let mut bits = Vec::with_capacity(n);
                for _ in 0..n { bits.push(1); }
                let count = rng.gen_range_usize(0, (n / 10).max(1));
                for _ in 0..count {
                    let p = rng.gen_range_usize(0, n - 1);
                    bits[p] = 0;
                }
                // ensure at least one 1
                let mut one_idx = 0usize;
                let mut found = false;
                for i in 0..n {
                    if bits[i] == 1 { one_idx = i; found = true; break; }
                }
                if !found {
                    bits[0] = 1;
                    one_idx = 0;
                }
                (bits, one_idx)
            }
        };

        let nums = generate_test_case(n, one_idx, &bits);
        print_json(&nums);
    }
}