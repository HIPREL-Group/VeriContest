use vstd::prelude::*;

verus! {

pub fn valid_permutation(raw: &Vec<i32>) -> (valid: bool)
    ensures valid ==> (
        1 <= raw.len() <= 1000
        && (forall|i: int| 0 <= i < raw.len() ==> 0 <= #[trigger] raw[i] < raw.len())
        && (forall|i: int, j: int| 0 <= i < j < raw.len() ==> raw[i] != raw[j])),
{
    if raw.len() == 0 || raw.len() > 1000 { return false; }
    let mut i = 0usize;
    while i < raw.len()
        invariant
            1 <= raw.len() <= 1000, 0 <= i <= raw.len(),
            forall|j: int| 0 <= j < i ==> 0 <= #[trigger] raw[j] < raw.len(),
            forall|j: int, k: int| 0 <= j < k < i ==> raw[j] != raw[k],
        decreases raw.len() - i,
    {
        if raw[i] < 0 || raw[i] as usize >= raw.len() { return false; }
        let mut j = 0usize;
        while j < i
            invariant
                0 <= j <= i < raw.len(),
                forall|k: int| 0 <= k < j ==> #[trigger] raw[k] != raw[i as int],
            decreases i - j,
        {
            if raw[j] == raw[i] { return false; }
            j += 1;
        }
        i += 1;
    }
    true
}

pub fn generate_test_case(raw: Vec<i32>) -> (result: Vec<i32>)
    ensures
        1 <= result.len() <= 1000,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] < result.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
{
    if valid_permutation(&raw) { return raw; }
    let n = if raw.len() == 0 { 1usize } else if raw.len() > 1000 { 1000usize } else { raw.len() };
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 1000, 0 <= i <= n, result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> #[trigger] result[j] == j,
        decreases n - i,
    {
        result.push(i as i32);
        i += 1;
    }
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 1000, 0 <= i <= n, result.len() == n,
            forall|j: int| 0 <= j < result.len() ==> 0 <= #[trigger] result[j] < n,
            forall|j: int, k: int| 0 <= j < k < result.len() ==> result[j] != result[k],
        decreases n - i,
    {
        let v = if i < raw.len() { raw[i] } else { i as i32 };
        let j = if v < 0 || v as usize >= n { i } else { v as usize };
        let a = result[i];
        let b = result[j];
        result.set(i, b);
        result.set(j, a);
        i += 1;
    }
    result
}


pub fn generate_candidate(perm: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= perm.len() <= 1000,
        forall|i: int| 0 <= i < perm.len() ==> 0 <= #[trigger] perm[i] < perm.len(),
    ensures
        1 <= nums.len() <= 1000,
        nums.len() == perm.len(),
        forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] < nums.len(),
{
    let n = perm.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == perm.len(),
            1 <= n <= 1000,
            0 <= i <= n,
            nums.len() == i,
            forall|k: int| 0 <= k < perm.len() ==> 0 <= #[trigger] perm[k] < perm.len(),
            forall|k: int| 0 <= k < i as int ==> #[trigger] nums[k] == perm[k],
        decreases n - i,
    {
        nums.push(perm[i]);
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
}

fn make_identity(n: usize) -> Vec<i32> {
    (0..n).map(|i| i as i32).collect()
}

fn make_reverse(n: usize) -> Vec<i32> {
    (0..n).map(|i| (n - 1 - i) as i32).collect()
}

fn make_rotate(n: usize, k: usize) -> Vec<i32> {
    (0..n).map(|i| ((i + k) % n) as i32).collect()
}

fn make_swap_pairs(n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = (0..n).map(|i| i as i32).collect();
    let mut i = 0;
    while i + 1 < n {
        v.swap(i, i + 1);
        i += 2;
    }
    v
}

fn make_random(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = (0..n).map(|i| i as i32).collect();
    // Fisher-Yates
    let mut i = n;
    while i > 1 {
        i -= 1;
        let j = rng.gen_range_usize(0, i);
        v.swap(i, j);
    }
    v
}

fn make_cycle(n: usize) -> Vec<i32> {
    // single big cycle: i -> (i+1) % n
    (0..n).map(|i| ((i + 1) % n) as i32).collect()
}

fn make_involution(n: usize) -> Vec<i32> {
    // swap i with n-1-i
    (0..n).map(|i| (n - 1 - i) as i32).collect()
}

fn print_json(nums: &[i32]) {
        let nums = generate_test_case(nums.to_vec());
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

    let total = 210usize;

    for t in 0..total {
        let mode = t % 10;
        let n: usize = match mode {
            0 => 1,
            1 => 2,
            2 => 1000,
            3 => 3 + (t % 10),
            4 => 50,
            5 => 100,
            6 => 500,
            7 => 999,
            8 => 1000,
            _ => 2 + rng.gen_range_usize(0, 200),
        };

        let perm: Vec<i32> = match mode {
            0 => make_identity(n),
            1 => make_reverse(n),
            2 => make_rotate(n, rng.gen_range_usize(0, if n > 0 { n - 1 } else { 0 })),
            3 => make_swap_pairs(n),
            4 => make_cycle(n),
            5 => make_involution(n),
            6 => make_random(&mut rng, n),
            7 => make_random(&mut rng, n),
            8 => make_random(&mut rng, n),
            _ => make_random(&mut rng, n),
        };

        let nums = generate_candidate(&perm);
        print_json(&nums);
    }
}
