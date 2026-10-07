use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32, raw_left: Vec<i32>, raw_right: Vec<i32>) -> (result: (i32, Vec<i32>, Vec<i32>))
    ensures 1 <= result.0 <= 10000, 1 <= result.1.len() + result.2.len() <= result.0 + 1,
        forall|i: int| 0 <= i < result.1.len() ==> 0 <= #[trigger] result.1[i] <= result.0,
        forall|i: int| 0 <= i < result.2.len() ==> 0 <= #[trigger] result.2[i] <= result.0,
        forall|i: int, j: int| 0 <= i < j < result.1.len() ==> result.1[i] != result.1[j],
        forall|i: int, j: int| 0 <= i < j < result.2.len() ==> result.2[i] != result.2[j],
        forall|i: int, j: int| 0 <= i < result.1.len() && 0 <= j < result.2.len() ==> result.1[i] != result.2[j],
{
    let n = if n < 1 { 1 } else if n > 10000 { 10000 } else { n };
    let mut seen: Vec<bool> = Vec::new();
    let mut i = 0usize;
    while i <= n as usize
        invariant i <= n + 1, 1 <= n <= 10000, seen.len() == i,
        decreases n + 1 - i,
    { seen.push(false); i += 1; }
    let mut left: Vec<i32> = Vec::new();
    let end = if raw_left.len() > n as usize + 1 { n as usize + 1 } else { raw_left.len() };
    let mut i = 0usize;
    while i < end
        invariant i <= end <= raw_left.len(), end <= n + 1, 1 <= n <= 10000,
            seen.len() == n + 1, left.len() <= i,
            forall|j: int| 0 <= j < left.len() ==> 0 <= #[trigger] left[j] <= n,
            forall|j: int| 0 <= j < left.len() ==> #[trigger] seen[left[j] as int],
            forall|j: int, k: int| 0 <= j < k < left.len() ==> left[j] != left[k],
        decreases end - i,
    {
        let v = raw_left[i];
        let v = if v < 0 { 0 } else if v > n { n } else { v };
        if !seen[v as usize] {
            assert forall|j: int| 0 <= j < left.len() implies #[trigger] left[j] != v by { assert(seen[left[j] as int]); }
            seen.set(v as usize, true); left.push(v);
        }
        i += 1;
    }
    let mut right: Vec<i32> = Vec::new();
    let end = if raw_right.len() > n as usize + 1 { n as usize + 1 } else { raw_right.len() };
    let mut i = 0usize;
    while i < end && left.len() + right.len() < n as usize + 1
        invariant i <= end <= raw_right.len(), end <= n + 1, 1 <= n <= 10000,
            seen.len() == n + 1, left.len() + right.len() <= n + 1,
            forall|j: int| 0 <= j < left.len() ==> 0 <= #[trigger] left[j] <= n,
            forall|j: int| 0 <= j < right.len() ==> 0 <= #[trigger] right[j] <= n,
            forall|j: int| 0 <= j < left.len() ==> #[trigger] seen[left[j] as int],
            forall|j: int| 0 <= j < right.len() ==> #[trigger] seen[right[j] as int],
            forall|j: int, k: int| 0 <= j < k < left.len() ==> left[j] != left[k],
            forall|j: int, k: int| 0 <= j < k < right.len() ==> right[j] != right[k],
            forall|j: int, k: int| 0 <= j < left.len() && 0 <= k < right.len() ==> left[j] != right[k],
        decreases end - i,
    {
        let v = raw_right[i];
        let v = if v < 0 { 0 } else if v > n { n } else { v };
        if !seen[v as usize] {
            assert forall|j: int| 0 <= j < left.len() implies #[trigger] left[j] != v by { assert(seen[left[j] as int]); }
            assert forall|j: int| 0 <= j < right.len() implies #[trigger] right[j] != v by { assert(seen[right[j] as int]); }
            seen.set(v as usize, true); right.push(v);
        }
        i += 1;
    }
    if left.len() + right.len() == 0 { left.push(0); }
    (n, left, right)
}


pub fn generate_candidate(
    n: i32,
    left: Vec<i32>,
    right: Vec<i32>,
) -> (res: (i32, Vec<i32>, Vec<i32>))
    requires
        1 <= n <= 10_000,
        left.len() + right.len() >= 1,
        left.len() + right.len() <= n + 1,
        forall |i: int| 0 <= i < left.len() ==> 0 <= #[trigger] left[i] <= n,
        forall |i: int| 0 <= i < right.len() ==> 0 <= #[trigger] right[i] <= n,
    ensures
        ({
            let (nn, l, r) = res;
            &&& 1 <= nn <= 10_000
            &&& l.len() + r.len() >= 1
            &&& l.len() + r.len() <= nn + 1
            &&& forall |i: int| 0 <= i < l.len() ==> 0 <= #[trigger] l[i] <= nn
            &&& forall |i: int| 0 <= i < r.len() ==> 0 <= #[trigger] r[i] <= nn
        }),
{
    (n, left, right)
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
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

// Build a test case by partitioning positions 0..=n among left, right.
// Each position can appear in at most one array.
fn make_case(rng: &mut Rng, n: i32, left_count: usize, right_count: usize) -> (i32, Vec<i32>, Vec<i32>) {
    let total_positions = (n + 1) as usize;
    // generate permutation of 0..=n and split
    let mut perm: Vec<i32> = (0..=n).collect();
    // Fisher-Yates
    for i in (1..perm.len()).rev() {
        let j = rng.gen_range_usize(0, i);
        perm.swap(i, j);
    }
    let total = left_count + right_count;
    let total = total.min(total_positions);
    let lc = left_count.min(total);
    let rc = total - lc;
    let left: Vec<i32> = perm[0..lc].to_vec();
    let right: Vec<i32> = perm[lc..lc+rc].to_vec();
    (n, left, right)
}

fn print_json(n: i32, left: &[i32], right: &[i32]) {
    let (n, left, right) = generate_test_case(n, left.to_vec(), right.to_vec());
    print!("{{\"n\":{},\"left\":[", n);
    for i in 0..left.len() {
        if i > 0 { print!(","); }
        print!("{}", left[i]);
    }
    print!("],\"right\":[");
    for i in 0..right.len() {
        if i > 0 { print!(","); }
        print!("{}", right[i]);
    }
    println!("]}}");
}

fn gen_for_mode(rng: &mut Rng, mode: usize, idx: usize) -> (i32, Vec<i32>, Vec<i32>) {
    match mode {
        0 => {
            // minimal n=1
            let n = 1;
            let total = rng.gen_range_usize(1, 2);
            let lc = rng.gen_range_usize(0, total);
            make_case(rng, n, lc, total - lc)
        }
        1 => {
            // max n with full capacity
            let n = 10_000;
            let total = (n + 1) as usize;
            let lc = rng.gen_range_usize(0, total);
            make_case(rng, n, lc, total - lc)
        }
        2 => {
            // all left, at positions forcing max
            let n = rng.gen_range_i32(1, 100);
            let total = rng.gen_range_usize(1, (n + 1) as usize);
            make_case(rng, n, total, 0)
        }
        3 => {
            // all right
            let n = rng.gen_range_i32(1, 100);
            let total = rng.gen_range_usize(1, (n + 1) as usize);
            make_case(rng, n, 0, total)
        }
        4 => {
            // single ant left at n
            let n = rng.gen_range_i32(1, 1000);
            let mut left = Vec::new();
            left.push(n);
            let right = Vec::new();
            (n, left, right)
        }
        5 => {
            // single ant right at 0
            let n = rng.gen_range_i32(1, 1000);
            let left = Vec::new();
            let mut right = Vec::new();
            right.push(0);
            (n, left, right)
        }
        6 => {
            // single ant at 0 (left) - answer 0
            let n = rng.gen_range_i32(1, 1000);
            let mut left = Vec::new();
            left.push(0);
            let right = Vec::new();
            (n, left, right)
        }
        7 => {
            // small random
            let n = rng.gen_range_i32(1, 20);
            let total = rng.gen_range_usize(1, (n + 1) as usize);
            let lc = rng.gen_range_usize(0, total);
            make_case(rng, n, lc, total - lc)
        }
        8 => {
            // medium
            let n = rng.gen_range_i32(100, 5000);
            let total = rng.gen_range_usize(1, (n + 1) as usize);
            let lc = rng.gen_range_usize(0, total);
            make_case(rng, n, lc, total - lc)
        }
        9 => {
            // boundary: only endpoints
            let n = rng.gen_range_i32(2, 1000);
            let r = idx % 4;
            match r {
                0 => {
                    let mut left = Vec::new(); left.push(0);
                    let right = Vec::new();
                    (n, left, right)
                }
                1 => {
                    let left = Vec::new();
                    let mut right = Vec::new(); right.push(n);
                    (n, left, right)
                }
                2 => {
                    let mut left = Vec::new(); left.push(n);
                    let mut right = Vec::new(); right.push(0);
                    (n, left, right)
                }
                _ => {
                    let mut left = Vec::new(); left.push(0); left.push(n);
                    let right = Vec::new();
                    (n, left, right)
                }
            }
        }
        _ => {
            let n = rng.gen_range_i32(1, 10_000);
            let total = rng.gen_range_usize(1, (n + 1) as usize);
            let lc = rng.gen_range_usize(0, total);
            make_case(rng, n, lc, total - lc)
        }
    }
}

fn validate(n: i32, left: &[i32], right: &[i32]) -> bool {
    if n < 1 || n > 10_000 { return false; }
    let tot = left.len() + right.len();
    if tot < 1 || tot as i32 > n + 1 { return false; }
    for &v in left { if v < 0 || v > n { return false; } }
    for &v in right { if v < 0 || v > n { return false; } }
    true
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
        let (n, left, right) = gen_for_mode(&mut rng, mode, t);
        if !validate(n, &left, &right) {
            // skip invalid (shouldn't happen)
            continue;
        }
        let (nn, l, r) = generate_candidate(n, left, right);
        print_json(nn, &l, &r);
    }
}
