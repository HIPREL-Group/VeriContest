use vstd::prelude::*;

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn binary_val(nums: Seq<i32>, len: nat) -> int
        decreases len,
    {
        if len == 0 {
            0
        } else {
            Self::binary_val(nums, (len - 1) as nat) * 2 + nums[(len - 1) as int] as int
        }
    }
}

pub fn generate_test_case(prefix: &Vec<i32>, suffix: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        0 <= prefix.len() <= 100_000,
        0 <= suffix.len() <= 100_000,
        prefix.len() + suffix.len() >= 1,
        prefix.len() + suffix.len() <= 100_000,
        forall|i: int| 0 <= i < prefix.len() ==> (#[trigger] prefix[i] == 0 || prefix[i] == 1),
        forall|i: int| 0 <= i < suffix.len() ==> (#[trigger] suffix[i] == 0 || suffix[i] == 1),
    ensures
        1 <= nums.len() <= 100_000,
        forall|i: int| 0 <= i < nums.len() ==> (#[trigger] nums[i] == 0 || nums[i] == 1),
{
    let total_len: usize = prefix.len() + suffix.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;

    while i < prefix.len()
        invariant
            total_len == prefix.len() + suffix.len(),
            1 <= total_len <= 100_000,
            0 <= i <= prefix.len(),
            nums.len() == i,
            forall|k: int| 0 <= k < prefix.len() ==> (#[trigger] prefix[k] == 0 || prefix[k] == 1),
            forall|k: int| 0 <= k < suffix.len() ==> (#[trigger] suffix[k] == 0 || suffix[k] == 1),
            forall|k: int| 0 <= k < i ==> nums[k] == prefix[k],
            forall|k: int| 0 <= k < nums.len() ==> (#[trigger] nums[k] == 0 || nums[k] == 1),
        decreases prefix.len() - i,
    {
        nums.push(prefix[i]);
        i = i + 1;
    }

    let mut j: usize = 0;
    while j < suffix.len()
        invariant
            total_len == prefix.len() + suffix.len(),
            1 <= total_len <= 100_000,
            0 <= j <= suffix.len(),
            nums.len() == prefix.len() + j,
            forall|k: int| 0 <= k < prefix.len() ==> (#[trigger] prefix[k] == 0 || prefix[k] == 1),
            forall|k: int| 0 <= k < suffix.len() ==> (#[trigger] suffix[k] == 0 || suffix[k] == 1),
            forall|k: int| 0 <= k < prefix.len() ==> nums[k] == prefix[k],
            forall|k: int| 0 <= k < j ==> nums[prefix.len() as int + k] == suffix[k],
            forall|k: int| 0 <= k < nums.len() ==> (#[trigger] nums[k] == 0 || nums[k] == 1),
        decreases suffix.len() - j,
    {
        nums.push(suffix[j]);
        j = j + 1;
    }

    assert(nums.len() == total_len);
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
        self.state = self
            .state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_bit(&mut self) -> i32 {
        (self.next_u64() & 1) as i32
    }
}

fn make_bits(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_bit());
    }
    v
}

fn all_zeros(len: usize) -> Vec<i32> {
    vec![0; len]
}

fn all_ones(len: usize) -> Vec<i32> {
    vec![1; len]
}

fn alternating(len: usize, first: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for i in 0..len {
        v.push(if i % 2 == 0 { first } else { 1 - first });
    }
    v
}

fn one_hot(len: usize, pos: usize) -> Vec<i32> {
    let mut v = vec![0; len];
    if len > 0 {
        v[pos] = 1;
    }
    v
}

fn prefix_suffix_case(mode: usize, rng: &mut Rng) -> (Vec<i32>, Vec<i32>) {
    match mode {
        0 => {
            let n = 1;
            (vec![0], vec![])
        }
        1 => {
            let n = 1;
            (vec![1], vec![])
        }
        2 => {
            let n = 100_000;
            (all_zeros(n), vec![])
        }
        3 => {
            let n = 100_000;
            (all_ones(n), vec![])
        }
        4 => {
            let n = 100_000;
            (alternating(n, 0), vec![])
        }
        5 => {
            let n = 100_000;
            (alternating(n, 1), vec![])
        }
        6 => {
            let n = 100_000;
            (one_hot(n, 0), vec![])
        }
        7 => {
            let n = 100_000;
            (one_hot(n, n - 1), vec![])
        }
        8 => {
            let n = 100_000;
            let mid = n / 2;
            (all_zeros(mid), all_ones(n - mid))
        }
        9 => {
            let n = 100_000;
            let mid = n / 2;
            (all_ones(mid), all_zeros(n - mid))
        }
        10 => {
            let n = rng.gen_range_usize(1, 100_000);
            let split = rng.gen_range_usize(0, n);
            (make_bits(rng, split), make_bits(rng, n - split))
        }
        11 => {
            let n = rng.gen_range_usize(1, 100_000);
            let split = if n >= 2 { 1 } else { 0 };
            let mut a = vec![1];
            if n > 1 {
                let mut b = all_zeros(n - 1);
                (a, b)
            } else {
                (a, vec![])
            }
        }
        _ => {
            let n = rng.gen_range_usize(1, 100_000);
            let split = rng.gen_range_usize(0, n);
            let mut left = make_bits(rng, split);
            let mut right = make_bits(rng, n - split);
            if n >= 5 {
                if left.len() >= 5 {
                    left[0] = 1;
                    left[1] = 0;
                    left[2] = 1;
                    left[3] = 0;
                    left[4] = 1;
                } else {
                    let pattern = [1, 0, 1, 0, 1];
                    let mut merged = Vec::with_capacity(n);
                    for i in 0..n {
                        merged.push(pattern[i % 5]);
                    }
                    let s = split;
                    left = merged[..s].to_vec();
                    right = merged[s..].to_vec();
                }
            }
            (left, right)
        }
    }
}

fn print_json(nums: &Vec<i32>) {
    use std::io::Write;
    let stdout = std::io::stdout();
    let mut out = std::io::BufWriter::new(stdout.lock());
    write!(out, "{{\"nums\":[").unwrap();
    for i in 0..nums.len() {
        if i > 0 {
            write!(out, ",").unwrap();
        }
        write!(out, "{}", nums[i]).unwrap();
    }
    writeln!(out, "]}}").unwrap();
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = if args.len() >= 2 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let total_cases = 200usize;

    for t in 0..total_cases {
        let mode = if t < 130 {
            t % 13
        } else {
            10 + (rng.next_u64() as usize % 3)
        };
        let (prefix, suffix) = prefix_suffix_case(mode, &mut rng);
        let nums = generate_test_case(&prefix, &suffix);
        print_json(&nums);
    }
}