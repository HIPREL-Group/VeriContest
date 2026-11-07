use vstd::prelude::*;

verus! {

spec fn filler_index(k: int, idx_a: int, idx_b: int) -> int {
    k - (if idx_a < k { 1int } else { 0int })
      - (if idx_b < k { 1int } else { 0int })
}

pub fn generate_test_case(
    a_val: i32,
    b_val: i32,
    idx_a: usize,
    idx_b: usize,
    fillers: &Vec<i32>,
    target: i32,
) -> (nums: Vec<i32>)
    requires
        a_val as int + b_val as int == target as int,
        -1_000_000_000 <= a_val <= 1_000_000_000,
        -1_000_000_000 <= b_val <= 1_000_000_000,
        -1_000_000_000 <= target <= 1_000_000_000,
        fillers.len() + 2 >= 2,
        fillers.len() + 2 <= 10_000,
        idx_a < fillers.len() + 2,
        idx_b < fillers.len() + 2,
        idx_a != idx_b,
        forall|i: int| 0 <= i < fillers.len() ==>
            -1_000_000_000 <= #[trigger] fillers[i] <= 1_000_000_000,
        forall|i: int| 0 <= i < fillers.len() ==>
            fillers[i] != a_val && fillers[i] != b_val,
        forall|i: int| 0 <= i < fillers.len() ==> (
            (#[trigger] fillers[i]) as int + a_val as int != target as int
            && fillers[i] as int + b_val as int != target as int
        ),
        forall|i: int, j: int|
            0 <= i < fillers.len() && 0 <= j < fillers.len() && i != j
                ==> (#[trigger] fillers[i]) as int + (#[trigger] fillers[j]) as int != target as int,
    ensures
        2 <= nums.len() <= 10_000,
        -1_000_000_000 <= target <= 1_000_000_000,
        forall|i: int|
            0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
        exists|i: int, j: int|
            0 <= i < nums.len() && 0 <= j < nums.len() && i != j && nums[i] + nums[j] == target,
        forall|i1: int, j1: int, i2: int, j2: int|
            0 <= i1 < nums.len() && 0 <= j1 < nums.len() && i1 != j1 && 0 <= i2 < nums.len()
                && 0 <= j2 < nums.len() && i2 != j2 && nums[i1] + nums[j1] == target
                && nums[i2] + nums[j2] == target ==> (i1 == i2 && j1 == j2) || (i1 == j2
                && j1 == i2),
{
    let n: usize = fillers.len() + 2;
    let mut nums: Vec<i32> = Vec::new();
    let mut fi: usize = 0;
    let mut pos: usize = 0;

    while pos < n
        invariant
            n == fillers.len() + 2,
            2 <= n <= 10_000,
            0 <= pos <= n,
            nums.len() == pos,
            idx_a < n,
            idx_b < n,
            idx_a != idx_b,
            0 <= fi <= fillers.len(),
            fi == pos - (if idx_a < pos { 1usize } else { 0usize })
                      - (if idx_b < pos { 1usize } else { 0usize }),
            forall|k: int| 0 <= k < pos as int && k == idx_a as int ==>
                #[trigger] nums[k] == a_val,
            forall|k: int| 0 <= k < pos as int && k == idx_b as int ==>
                #[trigger] nums[k] == b_val,
            forall|k: int| 0 <= k < pos as int && k != idx_a as int && k != idx_b as int ==>
                #[trigger] nums[k] == fillers[filler_index(k, idx_a as int, idx_b as int)],
            forall|k: int| 0 <= k < pos as int ==>
                -1_000_000_000 <= #[trigger] nums[k] <= 1_000_000_000,
            a_val as int + b_val as int == target as int,
            -1_000_000_000 <= a_val <= 1_000_000_000,
            -1_000_000_000 <= b_val <= 1_000_000_000,
            -1_000_000_000 <= target <= 1_000_000_000,
            forall|i: int| 0 <= i < fillers.len() ==>
                -1_000_000_000 <= #[trigger] fillers[i] <= 1_000_000_000,
            forall|i: int| 0 <= i < fillers.len() ==>
                fillers[i] != a_val && fillers[i] != b_val,
            forall|i: int| 0 <= i < fillers.len() ==> (
                (#[trigger] fillers[i]) as int + a_val as int != target as int
                && fillers[i] as int + b_val as int != target as int
            ),
            forall|i: int, j: int|
                0 <= i < fillers.len() && 0 <= j < fillers.len() && i != j
                    ==> (#[trigger] fillers[i]) as int + (#[trigger] fillers[j]) as int != target as int,
        decreases n - pos,
    {
        if pos == idx_a {
            nums.push(a_val);
        } else if pos == idx_b {
            nums.push(b_val);
        } else {
            assert(fi < fillers.len());
            assert(fi as int == filler_index(pos as int, idx_a as int, idx_b as int));
            nums.push(fillers[fi]);
            fi = fi + 1;
        }
        pos = pos + 1;
    }

    proof {
        assert(nums[idx_a as int] == a_val);
        assert(nums[idx_b as int] == b_val);
        assert(nums[idx_a as int] + nums[idx_b as int] == target);

        assert forall|i1: int, j1: int|
            0 <= i1 < nums.len() && 0 <= j1 < nums.len() && i1 != j1
                && nums[i1] + nums[j1] == target
            implies
            (i1 == idx_a as int && j1 == idx_b as int)
                || (i1 == idx_b as int && j1 == idx_a as int)
        by {
            let fi1 = filler_index(i1, idx_a as int, idx_b as int);
            let fj1 = filler_index(j1, idx_a as int, idx_b as int);
            if i1 == idx_a as int {
                if j1 != idx_b as int {
                    assert(nums[j1] == fillers[fj1]);
                    assert(fillers[fj1] as int + a_val as int != target as int);
                }
            } else if i1 == idx_b as int {
                if j1 != idx_a as int {
                    assert(nums[j1] == fillers[fj1]);
                    assert(fillers[fj1] as int + b_val as int != target as int);
                }
            } else {
                assert(nums[i1] == fillers[fi1]);
                if j1 == idx_a as int {
                    assert(fillers[fi1] as int + a_val as int != target as int);
                } else if j1 == idx_b as int {
                    assert(fillers[fi1] as int + b_val as int != target as int);
                } else {
                    assert(nums[j1] == fillers[fj1]);
                    assert(fi1 != fj1);
                    assert(fillers[fi1] as int + fillers[fj1] as int != target as int);
                }
            }
        }

        assert(exists|i: int, j: int|
            0 <= i < nums.len() && 0 <= j < nums.len() && i != j && nums[i] + nums[j] == target);
        assert forall|i1: int, j1: int, i2: int, j2: int|
            0 <= i1 < nums.len() && 0 <= j1 < nums.len() && i1 != j1 && 0 <= i2 < nums.len()
                && 0 <= j2 < nums.len() && i2 != j2 && nums[i1] + nums[j1] == target
                && nums[i2] + nums[j2] == target
            implies
                (i1 == i2 && j1 == j2) || (i1 == j2 && j1 == i2)
        by {
            assert((i1 == idx_a as int && j1 == idx_b as int)
                || (i1 == idx_b as int && j1 == idx_a as int));
            assert((i2 == idx_a as int && j2 == idx_b as int)
                || (i2 == idx_b as int && j2 == idx_a as int));
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
        Self { state: seed }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        let span = (hi as i128 - lo as i128 + 1) as u128;
        let v = (self.next_u64() as u128) % span;
        lo + v as i64
    }
}

fn choose_distinct_indices(rng: &mut Rng, n: usize) -> (usize, usize) {
    let i = rng.gen_range_usize(0, n - 1);
    let mut j = rng.gen_range_usize(0, n - 2);
    if j >= i {
        j += 1;
    }
    (i, j)
}

fn pick_pair_for_mode(rng: &mut Rng, mode: usize, n: usize) -> (i32, i32, i32, usize, usize) {
    match mode {
        0 => {
            let a = rng.gen_range_i64(-500_000_000, 500_000_000);
            let b = rng.gen_range_i64(-500_000_000, 500_000_000);
            (a as i32, b as i32, (a + b) as i32, 0, 1)
        }
        1 => {
            let a = rng.gen_range_i64(-500_000_000, 500_000_000);
            let b = rng.gen_range_i64(-500_000_000, 500_000_000);
            (a as i32, b as i32, (a + b) as i32, n - 2, n - 1)
        }
        2 => {
            let a = rng.gen_range_i64(-500_000_000, 500_000_000);
            let b = rng.gen_range_i64(-500_000_000, 500_000_000);
            (a as i32, b as i32, (a + b) as i32, 0, n - 1)
        }
        3 => {
            let x = rng.gen_range_i64(-500_000_000, 500_000_000);
            let (i, j) = choose_distinct_indices(rng, n);
            (x as i32, x as i32, (x * 2) as i32, i, j)
        }
        4 => {
            let x = rng.gen_range_i64(1, 1_000_000_000);
            let (i, j) = choose_distinct_indices(rng, n);
            (x as i32, (-x) as i32, 0i32, i, j)
        }
        5 => {
            let a = rng.gen_range_i64(-500_000_000, -1);
            let b = rng.gen_range_i64(-500_000_000, -1);
            let (i, j) = choose_distinct_indices(rng, n);
            (a as i32, b as i32, (a + b) as i32, i, j)
        }
        6 => {
            let a = 1_000_000_000i64;
            let b = rng.gen_range_i64(-1_000_000_000, 0);
            let (i, j) = choose_distinct_indices(rng, n);
            (a as i32, b as i32, (a + b) as i32, i, j)
        }
        7 => {
            let a = -1_000_000_000i64;
            let b = rng.gen_range_i64(0, 1_000_000_000);
            let (i, j) = choose_distinct_indices(rng, n);
            (a as i32, b as i32, (a + b) as i32, i, j)
        }
        8 => {
            let (i, j) = choose_distinct_indices(rng, n);
            (1_000_000_000i32, -1_000_000_000i32, 0i32, i, j)
        }
        9 => {
            let b = rng.gen_range_i64(-1_000_000_000, 1_000_000_000);
            let (i, j) = choose_distinct_indices(rng, n);
            (0i32, b as i32, b as i32, i, j)
        }
        _ => {
            let base = rng.gen_range_i64(-300_000_000, 300_000_000);
            let a = base;
            let b = base + 1;
            let (i, j) = choose_distinct_indices(rng, n);
            (a as i32, b as i32, (a + b) as i32, i, j)
        }
    }
}

fn make_fillers(count: usize, a: i32, b: i32, target: i32) -> Vec<i32> {
    let mut res = Vec::with_capacity(count);
    let mut x: i64 = -999_999_937;
    while res.len() < count {
        let v = x as i32;
        if v != a && v != b {
            let s1 = v as i64 + a as i64;
            let s2 = v as i64 + b as i64;
            if s1 != target as i64 && s2 != target as i64 {
                let mut ok = true;
                for &u in &res {
                    if u as i64 + v as i64 == target as i64 {
                        ok = false;
                        break;
                    }
                }
                if ok {
                    res.push(v);
                }
            }
        }
        x += 2;
        if x > 999_999_937 {
            x = -999_999_937 + (res.len() as i64 % 2);
        }
    }
    res
}

fn print_json(nums: &[i32], target: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", nums[i]);
    }
    println!("],\"target\":{}}}", target);
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
        let n = match mode {
            0 => 2 + (t % 4),
            1 => 10_000,
            2 => 17,
            3 => if t % 2 == 0 { 2 } else { 256 },
            4 => 3 + (t % 7),
            5 => 64,
            6 => 511,
            7 => 997,
            8 => 10_000,
            9 => 50,
            _ => 500 + (t % 100),
        };

        let (a, b, target, idx_a, idx_b) = pick_pair_for_mode(&mut rng, mode, n);
        let fillers = make_fillers(n - 2, a, b, target);
        let nums = generate_test_case(a, b, idx_a, idx_b, &fillers, target);
        print_json(&nums, target);
    }
}