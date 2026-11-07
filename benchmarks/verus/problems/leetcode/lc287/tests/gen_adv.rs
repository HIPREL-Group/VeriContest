use vstd::prelude::*;

verus! {

spec fn filler_index(k: int, dup_idx: int) -> int {
    k - (if dup_idx < k { 1int } else { 0int })
}

pub fn generate_test_case(
    n: usize,
    dup_val: i32,
    dup_idx: usize,
    fillers: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= n <= 100_000,
        fillers.len() == n,
        1 <= dup_val,
        dup_val as int <= n as int,
        dup_idx < n + 1,
        forall|i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i],
        forall|i: int| 0 <= i < fillers.len() ==> #[trigger] fillers[i] as int <= n as int,
        // One filler entry equals dup_val (so dup appears twice in result);
        // all others are distinct and different from dup_val
        exists|i: int| 0 <= i < fillers.len() && fillers[i] == dup_val,
        forall|i: int, j: int|
            0 <= i < fillers.len() && 0 <= j < fillers.len() && i != j
                ==> #[trigger] fillers[i] != #[trigger] fillers[j] 
                    || fillers[i] == dup_val && fillers[j] == dup_val,
        // exactly one pair of duplicates in fillers and that pair is dup_val
        forall|i1: int, j1: int, i2: int, j2: int|
            0 <= i1 < j1 < fillers.len() &&
            0 <= i2 < j2 < fillers.len() &&
            fillers[i1] == fillers[j1] &&
            fillers[i2] == fillers[j2] ==> fillers[i1] == fillers[i2],
    ensures
        nums.len() == n + 1,
        1 <= nums.len() - 1 <= 100_000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= nums.len() - 1,
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] == nums[j],
        forall|i1: int, j1: int, i2: int, j2: int|
            0 <= i1 < j1 < nums.len() &&
            0 <= i2 < j2 < nums.len() &&
            nums[i1] == nums[j1] &&
            nums[i2] == nums[j2] ==> nums[i1] == nums[i2],
{
    let total: usize = n + 1;
    let mut nums: Vec<i32> = Vec::new();
    let mut fi: usize = 0;
    let mut pos: usize = 0;

    while pos < total
        invariant
            total == n + 1,
            1 <= n <= 100_000,
            fillers.len() == n,
            0 <= pos <= total,
            nums.len() == pos,
            dup_idx < total,
            0 <= fi <= fillers.len(),
            fi as int == filler_index(pos as int, dup_idx as int),
            1 <= dup_val,
            dup_val as int <= n as int,
            forall|i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i],
            forall|i: int| 0 <= i < fillers.len() ==> #[trigger] fillers[i] as int <= n as int,
            forall|k: int| 0 <= k < pos as int && k == dup_idx as int ==>
                #[trigger] nums[k] == dup_val,
            forall|k: int| 0 <= k < pos as int && k != dup_idx as int ==>
                #[trigger] nums[k] == fillers[filler_index(k, dup_idx as int)],
            forall|k: int| 0 <= k < pos as int ==>
                1 <= #[trigger] nums[k] && nums[k] as int <= n as int,
        decreases total - pos,
    {
        if pos == dup_idx {
            nums.push(dup_val);
        } else {
            assert(fi < fillers.len());
            nums.push(fillers[fi]);
            fi = fi + 1;
        }
        pos = pos + 1;
    }

    proof {
        assert(nums.len() == total);
        assert(nums.len() - 1 == n);

        // bounds
        assert forall|i: int| 0 <= i < nums.len() implies 1 <= #[trigger] nums[i] <= nums.len() - 1 by {
            assert(nums[i] as int <= n as int);
        }

        // existence of duplicate pair
        let fdup = choose|k: int| 0 <= k < fillers.len() && fillers[k] == dup_val;
        assert(0 <= fdup < fillers.len() && fillers[fdup] == dup_val);

        // Find position in nums where this filler was placed
        let pos_of_fdup: int = if fdup < dup_idx as int { fdup } else { fdup + 1 };
        assert(0 <= pos_of_fdup < nums.len());
        assert(pos_of_fdup != dup_idx as int);
        assert(filler_index(pos_of_fdup, dup_idx as int) == fdup);
        assert(nums[pos_of_fdup] == fillers[fdup]);
        assert(nums[pos_of_fdup] == dup_val);
        assert(nums[dup_idx as int] == dup_val);

        let ii = if pos_of_fdup < dup_idx as int { pos_of_fdup } else { dup_idx as int };
        let jj = if pos_of_fdup < dup_idx as int { dup_idx as int } else { pos_of_fdup };
        assert(0 <= ii < jj < nums.len());
        assert(nums[ii] == dup_val && nums[jj] == dup_val);
        assert(exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] == nums[j]);

        // uniqueness of the duplicate value
        assert forall|i1: int, j1: int, i2: int, j2: int|
            0 <= i1 < j1 < nums.len() &&
            0 <= i2 < j2 < nums.len() &&
            nums[i1] == nums[j1] &&
            nums[i2] == nums[j2]
            implies nums[i1] == nums[i2]
        by {
            // claim: nums[i1] == dup_val and nums[i2] == dup_val
            // Proof: if nums[i1] != dup_val, then both positions i1, j1 are filler positions
            // with distinct filler values (since fillers have only dup_val duplicated).
            // We show nums[i1] == dup_val.
            if i1 != dup_idx as int && j1 != dup_idx as int {
                let fi1 = filler_index(i1, dup_idx as int);
                let fj1 = filler_index(j1, dup_idx as int);
                assert(nums[i1] == fillers[fi1]);
                assert(nums[j1] == fillers[fj1]);
                assert(fi1 != fj1);
                assert(fillers[fi1] == fillers[fj1]);
                // by hypothesis, fillers[fi1] == dup_val
                assert(fillers[fi1] == dup_val);
            } else if i1 == dup_idx as int {
                assert(nums[i1] == dup_val);
            } else {
                // j1 == dup_idx
                assert(nums[j1] == dup_val);
                assert(nums[i1] == dup_val);
            }
            // same for i2, j2
            if i2 != dup_idx as int && j2 != dup_idx as int {
                let fi2 = filler_index(i2, dup_idx as int);
                let fj2 = filler_index(j2, dup_idx as int);
                assert(nums[i2] == fillers[fi2]);
                assert(nums[j2] == fillers[fj2]);
                assert(fi2 != fj2);
                assert(fillers[fi2] == fillers[fj2]);
                assert(fillers[fi2] == dup_val);
            } else if i2 == dup_idx as int {
                assert(nums[i2] == dup_val);
            } else {
                assert(nums[j2] == dup_val);
                assert(nums[i2] == dup_val);
            }
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
}

// Build fillers: a vector of length n with values in [1, n],
// containing dup_val exactly twice and each other value in [1,n]\{dup_val} exactly once
// except one omitted so total length is n.
// Actually fillers length must equal n, and {1..n} has n values. We need dup_val twice
// so we must omit one value v (v != dup_val). Then fillers contains dup_val twice
// plus all values in {1..n}\{dup_val, v}.
fn build_fillers(rng: &mut Rng, n: usize, dup_val: i32) -> Vec<i32> {
    // omit one value different from dup_val
    let omit: i32 = if n == 1 {
        // n==1, dup_val must be 1, fillers.len()==1, must contain dup_val once... 
        // but we need dup_val to appear twice across (nums), and nums.len()=n+1=2.
        // fillers.len()=1 and dup_idx is another position, so total occurrences of dup_val = 2.
        // That means fillers[0] must equal dup_val. So no omit issue; we just include dup_val.
        0
    } else {
        // pick v in [1..n], v != dup_val
        loop {
            let v = rng.gen_range_usize(1, n) as i32;
            if v != dup_val { break v; }
        }
    };

    let mut res: Vec<i32> = Vec::with_capacity(n);
    if n == 1 {
        res.push(dup_val);
        return res;
    }
    // Add dup_val twice, add all others except omit
    res.push(dup_val);
    res.push(dup_val);
    for v in 1..=n as i32 {
        if v != dup_val && v != omit {
            res.push(v);
        }
    }
    // shuffle
    let len = res.len();
    for i in (1..len).rev() {
        let j = rng.gen_range_usize(0, i);
        res.swap(i, j);
    }
    res
}

fn pick_params(rng: &mut Rng, mode: usize, t: usize) -> (usize, i32, usize) {
    let n: usize = match mode {
        0 => 1,
        1 => 2,
        2 => 3,
        3 => 10,
        4 => 100,
        5 => 1000,
        6 => 100_000,
        7 => 100_000,
        8 => rng.gen_range_usize(1, 50),
        9 => rng.gen_range_usize(50, 500),
        _ => rng.gen_range_usize(1, 1000),
    };
    let dup_val: i32 = match mode {
        0 => 1,
        1 => 1,
        2 => if t % 2 == 0 { 1 } else { n as i32 },
        3 => n as i32,
        4 => 1,
        5 => (n as i32) / 2 + 1,
        6 => 1,
        7 => n as i32,
        _ => rng.gen_range_usize(1, n) as i32,
    };
    let dup_idx = rng.gen_range_usize(0, n);
    (n, dup_val, dup_idx)
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
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);

    let total = 220usize;
    for t in 0..total {
        let mode = t % 11;
        let (n, dup_val, dup_idx) = pick_params(&mut rng, mode, t);
        let fillers = build_fillers(&mut rng, n, dup_val);
        let nums = generate_test_case(n, dup_val, dup_idx, &fillers);
        print_json(&nums);
    }
}