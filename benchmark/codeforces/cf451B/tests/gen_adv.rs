use vstd::prelude::*;

verus! {

pub open spec fn all_in_range(s: Seq<i64>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> 1 <= #[trigger] s[i] <= 1_000_000_000
}

pub open spec fn all_distinct(s: Seq<i64>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> #[trigger] s[i] != #[trigger] s[j]
}

pub fn generate_test_case(vals: &Vec<i64>) -> (nums: Vec<i64>)
    requires
        1 <= vals.len() <= 100_000,
        forall|i: int| 0 <= i < vals.len() ==> 1 <= #[trigger] vals[i] <= 1_000_000_000,
        forall|i: int, j: int| 0 <= i < j < vals.len() ==> #[trigger] vals[i] != #[trigger] vals[j],
    ensures
        1 <= nums.len() <= 100_000,
        nums.len() == vals.len(),
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
        forall|i: int, j: int| 0 <= i < j < nums.len() ==> #[trigger] nums[i] != #[trigger] nums[j],
{
    let mut nums: Vec<i64> = Vec::new();
    let n = vals.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == vals.len(),
            0 <= i <= n,
            nums.len() == i,
            forall|k: int| 0 <= k < i as int ==> #[trigger] nums[k] == vals[k],
            forall|k: int| 0 <= k < vals.len() ==> 1 <= #[trigger] vals[k] <= 1_000_000_000,
            forall|a: int, b: int| 0 <= a < b < vals.len() ==> #[trigger] vals[a] != #[trigger] vals[b],
        decreases n - i,
    {
        nums.push(vals[i]);
        i = i + 1;
    }
    assert(nums.len() == vals.len());
    assert forall|a: int, b: int| 0 <= a < b < nums.len() implies #[trigger] nums[a] != #[trigger] nums[b] by {
        assert(nums[a] == vals[a]);
        assert(nums[b] == vals[b]);
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
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i64
    }
}

// Build distinct values in [1, 1e9] of given length
fn make_distinct(rng: &mut Rng, n: usize, max_v: i64) -> Vec<i64> {
    // Use a shuffled range approach when n is not too huge; otherwise rejection.
    let mut used = std::collections::HashSet::new();
    let mut out = Vec::with_capacity(n);
    while out.len() < n {
        let v = rng.gen_range_i64(1, max_v);
        if used.insert(v) {
            out.push(v);
        }
    }
    out
}

fn sorted_ascending(n: usize) -> Vec<i64> {
    (1..=n as i64).collect()
}

fn build_mode(rng: &mut Rng, mode: usize, n: usize) -> Vec<i64> {
    let n = if n < 1 { 1 } else { n };
    match mode {
        0 => {
            // Fully sorted
            sorted_ascending(n)
        }
        1 => {
            // Fully reversed
            let mut v: Vec<i64> = (1..=n as i64).rev().collect();
            // ensure distinct (they are)
            v
        }
        2 => {
            // Sorted with a random segment reversed (YES answer)
            let mut v = sorted_ascending(n);
            if n >= 2 {
                let l = rng.gen_range_usize(0, n - 1);
                let r = rng.gen_range_usize(l, n - 1);
                v[l..=r].reverse();
            }
            v
        }
        3 => {
            // Reverse a prefix
            let mut v = sorted_ascending(n);
            if n >= 2 {
                let r = rng.gen_range_usize(1, n - 1);
                v[0..=r].reverse();
            }
            v
        }
        4 => {
            // Reverse a suffix
            let mut v = sorted_ascending(n);
            if n >= 2 {
                let l = rng.gen_range_usize(0, n - 2);
                v[l..n].reverse();
            }
            v
        }
        5 => {
            // Totally random (likely NO)
            make_distinct(rng, n, 1_000_000_000)
        }
        6 => {
            // Nearly sorted but with two far swaps (likely NO)
            let mut v = sorted_ascending(n);
            if n >= 4 {
                v.swap(0, 1);
                v.swap(n - 2, n - 1);
            }
            v
        }
        7 => {
            // Single element
            vec![rng.gen_range_i64(1, 1_000_000_000)]
        }
        8 => {
            // Size 2
            let a = rng.gen_range_i64(1, 1_000_000_000);
            let mut b = rng.gen_range_i64(1, 1_000_000_000);
            while b == a {
                b = rng.gen_range_i64(1, 1_000_000_000);
            }
            vec![a, b]
        }
        9 => {
            // Large values near bounds, sorted
            let mut v = Vec::with_capacity(n);
            let start: i64 = 1_000_000_000 - n as i64;
            for i in 0..n {
                v.push(start + i as i64);
            }
            // reverse random segment
            if n >= 2 && rng.next_u64() % 2 == 0 {
                let l = rng.gen_range_usize(0, n - 1);
                let r = rng.gen_range_usize(l, n - 1);
                v[l..=r].reverse();
            }
            v
        }
        _ => {
            // Sorted with adjacent swap (YES)
            let mut v = sorted_ascending(n);
            if n >= 2 {
                let l = rng.gen_range_usize(0, n - 2);
                v.swap(l, l + 1);
            }
            v
        }
    }
}

fn print_json(nums: &[i64]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);

    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match t % 13 {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => rng.gen_range_usize(4, 20),
            4 => rng.gen_range_usize(20, 100),
            5 => 100_000,
            6 => 99_999,
            7 => rng.gen_range_usize(1000, 5000),
            8 => rng.gen_range_usize(1, 50),
            9 => rng.gen_range_usize(50, 500),
            10 => rng.gen_range_usize(500, 5000),
            11 => 50_000,
            _ => rng.gen_range_usize(1, 1000),
        };
        let vals_plain = build_mode(&mut rng, mode, n);

        // Validate in plain rust: distinct and in range
        let mut ok = true;
        if vals_plain.is_empty() || vals_plain.len() > 100_000 { ok = false; }
        let mut seen = std::collections::HashSet::new();
        for &x in &vals_plain {
            if x < 1 || x > 1_000_000_000 { ok = false; break; }
            if !seen.insert(x) { ok = false; break; }
        }
        if !ok {
            // fallback to sorted ascending
            let v = sorted_ascending(n.max(1).min(100_000));
            let vals_vec: Vec<i64> = v;
            let nums = generate_test_case(&vals_vec);
            print_json(&nums);
            continue;
        }

        let vals_vec: Vec<i64> = vals_plain;
        let nums = generate_test_case(&vals_vec);
        print_json(&nums);
    }
}