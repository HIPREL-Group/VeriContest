use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, perm: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= n <= 100_000,
        perm.len() == n,
        forall |i: int| 0 <= i < perm.len() ==> 0 <= #[trigger] perm[i] < perm.len(),
        forall |i: int, j: int| #![trigger perm[i], perm[j]]
            0 <= i < j < perm.len() ==> perm[i] != perm[j],
    ensures
        1 <= nums.len() <= 100_000,
        forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] < nums.len(),
        forall |i: int, j: int| #![trigger nums[i], nums[j]]
            0 <= i < j < nums.len() ==> nums[i] != nums[j],
{
    let mut nums: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            n == perm.len(),
            0 <= k <= n,
            nums.len() == k,
            forall |i: int| 0 <= i < k as int ==> #[trigger] nums[i] == perm[i],
            forall |i: int| 0 <= i < perm.len() ==> 0 <= #[trigger] perm[i] < perm.len(),
        decreases n - k,
    {
        nums.push(perm[k]);
        k = k + 1;
    }

    assert(nums.len() == n);
    assert forall |i: int| 0 <= i < nums.len() implies 0 <= #[trigger] nums[i] < nums.len() by {
        assert(nums[i] == perm[i]);
    }
    assert forall |i: int, j: int|
        0 <= i < j < nums.len() implies #[trigger] nums[i] != #[trigger] nums[j] by {
        assert(nums[i] == perm[i]);
        assert(nums[j] == perm[j]);
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
}

fn identity_perm(n: usize) -> Vec<i32> {
    (0..n).map(|i| i as i32).collect()
}

fn reversed_perm(n: usize) -> Vec<i32> {
    (0..n).rev().map(|i| i as i32).collect()
}

fn swap_adjacent_all(n: usize) -> Vec<i32> {
    // swap pairs (0,1),(2,3),...
    let mut v: Vec<i32> = (0..n).map(|i| i as i32).collect();
    let mut i = 0;
    while i + 1 < n {
        v.swap(i, i + 1);
        i += 2;
    }
    v
}

fn swap_one_adjacent(n: usize, pos: usize) -> Vec<i32> {
    let mut v: Vec<i32> = (0..n).map(|i| i as i32).collect();
    if pos + 1 < n {
        v.swap(pos, pos + 1);
    }
    v
}

fn swap_nonadjacent(n: usize, i: usize, j: usize) -> Vec<i32> {
    let mut v: Vec<i32> = (0..n).map(|i| i as i32).collect();
    if i < n && j < n && i != j {
        v.swap(i, j);
    }
    v
}

fn random_perm(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = (0..n).map(|i| i as i32).collect();
    // Fisher-Yates
    for i in (1..n).rev() {
        let j = rng.gen_range_usize(0, i);
        v.swap(i, j);
    }
    v
}

fn random_ideal_perm(rng: &mut Rng, n: usize) -> Vec<i32> {
    // generate a permutation that only swaps adjacents with some probability
    let mut v: Vec<i32> = (0..n).map(|i| i as i32).collect();
    let mut i = 0;
    while i + 1 < n {
        if rng.next_u64() % 2 == 0 {
            v.swap(i, i + 1);
            i += 2;
        } else {
            i += 1;
        }
    }
    v
}

fn validate(n: usize, v: &Vec<i32>) -> bool {
    if v.len() != n { return false; }
    let mut seen = vec![false; n];
    for &x in v {
        if x < 0 || (x as usize) >= n { return false; }
        if seen[x as usize] { return false; }
        seen[x as usize] = true;
    }
    true
}

fn print_json(nums: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("]}}");
}

fn pick_test(rng: &mut Rng, mode: usize, t: usize) -> (usize, Vec<i32>) {
    match mode {
        0 => {
            let n = 1;
            (n, identity_perm(n))
        }
        1 => {
            let n = 2;
            if t % 2 == 0 { (n, identity_perm(n)) } else { (n, reversed_perm(n)) }
        }
        2 => {
            let n = 3 + (t % 8);
            (n, identity_perm(n))
        }
        3 => {
            let n = 3 + (t % 10);
            (n, reversed_perm(n))
        }
        4 => {
            let n = 2 + (t % 20);
            (n, swap_adjacent_all(n))
        }
        5 => {
            let n = 5 + (t % 30);
            let pos = rng.gen_range_usize(0, n - 2);
            (n, swap_one_adjacent(n, pos))
        }
        6 => {
            let n = 5 + (t % 50);
            let i = rng.gen_range_usize(0, n - 1);
            let mut j = rng.gen_range_usize(0, n - 2);
            if j >= i { j += 1; }
            // make sure non-adjacent when possible
            if n >= 3 && i + 1 != j && j + 1 != i {
                (n, swap_nonadjacent(n, i, j))
            } else {
                (n, swap_nonadjacent(n, 0, n - 1))
            }
        }
        7 => {
            let n = 1 + rng.gen_range_usize(1, 100);
            (n, random_perm(rng, n))
        }
        8 => {
            let n = 100 + rng.gen_range_usize(0, 900);
            (n, random_ideal_perm(rng, n))
        }
        9 => {
            let n = 100_000;
            (n, identity_perm(n))
        }
        _ => {
            let n = 50 + rng.gen_range_usize(0, 200);
            (n, random_perm(rng, n))
        }
    }
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
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let (n, perm) = pick_test(&mut rng, mode, t);
        if !validate(n, &perm) {
            // fallback
            let p = identity_perm(n.max(1));
            let nums = generate_test_case(p.len(), &p);
            print_json(&nums);
            continue;
        }
        let nums = generate_test_case(n, &perm);
        print_json(&nums);
    }
}