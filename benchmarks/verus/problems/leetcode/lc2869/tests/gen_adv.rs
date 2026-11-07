use vstd::prelude::*;

verus! {

pub open spec fn seen_in_suffix_spec(nums: Seq<i32>, v: int, ops: int) -> bool {
    exists |q: int|
        0 <= q < ops
        && 0 <= nums.len() - ops + q < nums.len()
        && #[trigger] nums[nums.len() - ops + q] == v
}

pub open spec fn all_seen_spec(nums: Seq<i32>, k: int, ops: int) -> bool {
    forall |v: int| 1 <= v <= k ==> seen_in_suffix_spec(nums, v, ops)
}

pub fn generate_test_case(
    n: usize,
    k: i32,
    positions: &Vec<usize>,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= n <= 50,
        1 <= k as int <= n as int,
        positions.len() == k as int,
        forall |i: int| 0 <= i < positions.len() ==> (#[trigger] positions[i]) < n,
        forall |i: int, j: int| 0 <= i < positions.len() && 0 <= j < positions.len() && i != j
            ==> #[trigger] positions[i] != #[trigger] positions[j],
    ensures
        ({
            let nums = result.0;
            let kk = result.1;
            &&& 1 <= nums.len() <= 50
            &&& nums.len() == n
            &&& kk == k
            &&& 1 <= kk as int <= nums.len() as int
            &&& (forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= nums.len())
            &&& all_seen_spec(nums@, kk as int, nums.len() as int)
        }),
{
    // Initialize nums with 1s
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            nums.len() == i,
            i <= n,
            n <= 50,
            forall |j: int| 0 <= j < nums.len() ==> #[trigger] nums[j] == 1i32,
        decreases n - i,
    {
        nums.push(1i32);
        i = i + 1;
    }

    // Place values 1..=k at positions[0..k]
    let mut idx: usize = 0;
    while idx < positions.len()
        invariant
            idx <= positions.len(),
            positions.len() == k as int,
            1 <= k as int <= n as int,
            nums.len() == n,
            n <= 50,
            forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= n as int,
            forall |t: int| 0 <= t < idx as int ==> 
                nums[positions[t] as int] == (t + 1) as i32,
            forall |i: int, j: int| 0 <= i < positions.len() && 0 <= j < positions.len() && i != j
                ==> #[trigger] positions[i] != #[trigger] positions[j],
            forall |i: int| 0 <= i < positions.len() ==> (#[trigger] positions[i]) < n,
        decreases positions.len() - idx,
    {
        let pos = positions[idx];
        let val: i32 = (idx + 1) as i32;
        assert(1 <= val <= k);
        assert(val as int <= n as int);
        
        // Prove previous placements are preserved
        let old_nums = nums;
        let mut new_nums = old_nums;
        new_nums.set(pos, val);
        
        proof {
            assert forall |t: int| 0 <= t < idx as int implies
                new_nums[positions[t] as int] == (t + 1) as i32
            by {
                assert(positions[t] != pos);
                assert(new_nums[positions[t] as int] == old_nums[positions[t] as int]);
            }
        }
        
        nums = new_nums;
        idx = idx + 1;
    }

    proof {
        // Now prove all_seen_spec
        assert forall |v: int| 1 <= v <= k as int implies
            seen_in_suffix_spec(nums@, v, nums.len() as int)
        by {
            let t = v - 1;
            assert(0 <= t < positions.len());
            let p = positions[t] as int;
            assert(nums[p] == v as i32);
            let q = p;  // since nums.len() - ops = 0
            assert(0 <= q < nums.len() as int);
            assert(nums.len() as int - nums.len() as int + q == q);
            assert(nums[nums.len() - nums.len() as int + q] == v as i32);
        }
    }

    (nums, k)
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
    fn gen_range(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
}

fn gen_permutation_prefix(rng: &mut Rng, n: usize, k: usize) -> Vec<usize> {
    let mut all: Vec<usize> = (0..n).collect();
    // Shuffle
    for i in (1..all.len()).rev() {
        let j = rng.gen_range(0, i);
        all.swap(i, j);
    }
    all.truncate(k);
    all
}

fn build_test(rng: &mut Rng, mode: usize, t: usize) -> (usize, i32, Vec<usize>) {
    let n: usize = match mode {
        0 => 1,
        1 => 50,
        2 => 2,
        3 => rng.gen_range(1, 50),
        4 => rng.gen_range(5, 15),
        5 => rng.gen_range(20, 50),
        6 => 3,
        7 => rng.gen_range(1, 10),
        8 => 50,
        9 => rng.gen_range(1, 50),
        _ => rng.gen_range(1, 50),
    };

    let k: usize = match mode {
        0 => 1,
        1 => 50,
        2 => if n >= 2 { 2 } else { 1 },
        3 => 1,
        4 => n,
        5 => rng.gen_range(1, n),
        6 => if n >= 2 { 2 } else { 1 },
        7 => n,
        8 => 1,
        9 => rng.gen_range(1, n),
        _ => {
            let kk = rng.gen_range(1, n);
            kk
        }
    };
    let _ = t;

    let positions = gen_permutation_prefix(rng, n, k);
    (n, k as i32, positions)
}

fn print_json(nums: &[i32], k: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("],\"k\":{}}}", k);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };

    let mut rng = Rng::new(seed);
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (n, k, positions) = build_test(&mut rng, mode, t);
        let pos_vec: Vec<usize> = positions;
        let (nums, kk) = generate_test_case(n, k, &pos_vec);
        print_json(&nums, kk);
    }
}