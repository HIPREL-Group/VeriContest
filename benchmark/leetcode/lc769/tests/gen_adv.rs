use vstd::prelude::*;

verus! {

pub fn valid_permutation(raw: &Vec<i32>) -> (valid: bool)
    ensures valid ==> (
        1 <= raw.len() <= 10
        && (forall|i: int| 0 <= i < raw.len() ==> 0 <= #[trigger] raw[i] < raw.len())
        && (forall|i: int, j: int| 0 <= i < j < raw.len() ==> raw[i] != raw[j])),
{
    if raw.len() == 0 || raw.len() > 10 { return false; }
    let mut i = 0usize;
    while i < raw.len()
        invariant
            1 <= raw.len() <= 10, 0 <= i <= raw.len(),
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
        1 <= result.len() <= 10,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] < result.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
{
    if valid_permutation(&raw) { return raw; }
    let n = if raw.len() == 0 { 1usize } else if raw.len() > 10 { 10usize } else { raw.len() };
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 10, 0 <= i <= n, result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> #[trigger] result[j] == j,
        decreases n - i,
    {
        result.push(i as i32);
        i += 1;
    }
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 10, 0 <= i <= n, result.len() == n,
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


pub fn generate_candidate(n: usize, perm: Vec<i32>) -> (arr: Vec<i32>)
    requires
        1 <= n <= 10,
        perm.len() == n,
        forall |i: int| 0 <= i < perm.len() ==> 0 <= #[trigger] perm[i] < n as i32,
    ensures
        1 <= arr.len() <= 10,
        forall |i: int| 0 <= i < arr.len() ==> 0 <= #[trigger] arr[i] < arr.len(),
{
    perm
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
}

fn identity_perm(n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    for i in 0..n {
        v.push(i as i32);
    }
    v
}

fn reverse_perm(n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    for i in 0..n {
        v.push((n - 1 - i) as i32);
    }
    v
}

fn random_perm(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = identity_perm(n);
    for i in (1..n).rev() {
        let j = rng.gen_range_usize(0, i);
        v.swap(i, j);
    }
    v
}

fn swap_adjacent_perm(n: usize, i: usize) -> Vec<i32> {
    let mut v = identity_perm(n);
    if i + 1 < n {
        v.swap(i, i + 1);
    }
    v
}

fn rotate_perm(n: usize, k: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    for i in 0..n {
        v.push(((i + k) % n) as i32);
    }
    v
}

fn two_chunks_perm(n: usize, split: usize) -> Vec<i32> {
    // first chunk is [0..split) reversed-ish, second chunk is [split..n)
    let mut v: Vec<i32> = Vec::with_capacity(n);
    if split > 0 {
        for i in 0..split {
            v.push((split - 1 - i) as i32);
        }
    }
    for i in split..n {
        v.push(i as i32);
    }
    v
}

fn single_swap_far(n: usize, rng: &mut Rng) -> Vec<i32> {
    let mut v = identity_perm(n);
    if n >= 2 {
        let i = rng.gen_range_usize(0, n - 1);
        let mut j = rng.gen_range_usize(0, n - 2);
        if j >= i { j += 1; }
        v.swap(i, j);
    }
    v
}

fn shifted_perm(n: usize) -> Vec<i32> {
    // [n-1, 0, 1, 2, ..., n-2]
    let mut v: Vec<i32> = Vec::with_capacity(n);
    if n > 0 {
        v.push((n - 1) as i32);
        for i in 0..n - 1 {
            v.push(i as i32);
        }
    }
    v
}

fn print_json(arr: &[i32]) {
        let arr = generate_test_case(arr.to_vec());
    print!("{{\"arr\":[");
    for i in 0..arr.len() {
        if i > 0 { print!(","); }
        print!("{}", arr[i]);
    }
    println!("]}}");
}

fn validate_and_fix(mut v: Vec<i32>, n: usize) -> Vec<i32> {
    // Guarantee length == n and each value in [0, n). If invalid, fallback to identity.
    if v.len() != n {
        return identity_perm(n);
    }
    for i in 0..v.len() {
        if v[i] < 0 || (v[i] as i64) >= n as i64 {
            return identity_perm(n);
        }
    }
    v
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
    let modes = 10usize;

    for t in 0..total {
        let mode = t % modes;
        let n: usize = match mode {
            0 => 1,
            1 => 2,
            2 => 10,
            3 => rng.gen_range_usize(1, 10),
            4 => rng.gen_range_usize(1, 10),
            5 => rng.gen_range_usize(2, 10),
            6 => rng.gen_range_usize(2, 10),
            7 => rng.gen_range_usize(1, 10),
            8 => rng.gen_range_usize(2, 10),
            _ => rng.gen_range_usize(1, 10),
        };

        let perm: Vec<i32> = match mode {
            0 => identity_perm(n),
            1 => reverse_perm(n),
            2 => random_perm(&mut rng, n),
            3 => {
                let i = if n > 1 { rng.gen_range_usize(0, n - 2) } else { 0 };
                swap_adjacent_perm(n, i)
            }
            4 => {
                let k = rng.gen_range_usize(0, n.saturating_sub(1).max(0));
                rotate_perm(n, k)
            }
            5 => {
                let s = rng.gen_range_usize(0, n);
                two_chunks_perm(n, s)
            }
            6 => single_swap_far(n, &mut rng),
            7 => shifted_perm(n),
            8 => reverse_perm(n),
            _ => random_perm(&mut rng, n),
        };

        let perm = validate_and_fix(perm, n);
        let arr = generate_candidate(n, perm);
        print_json(&arr);
    }
}
