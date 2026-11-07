use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    a_val: i32,
    b_val: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    ensures
        2 <= result.0.len() <= 30_000,
        -1_000 <= result.1 <= 1_000,
        forall|i: int|
            0 <= i < result.0.len() ==> -1_000 <= #[trigger] result.0[i] <= 1_000,
        forall |i: int, j: int|
            0 <= i < j < result.0.len() ==> result.0[i] <= result.0[j],
        exists|i: int, j: int|
            0 <= i < result.0.len() &&
            0 <= j < result.0.len() &&
            i != j &&
            result.0[i] + result.0[j] == result.1,
        forall|i1: int, j1: int, i2: int, j2: int|
            0 <= i1 < result.0.len() && 0 <= j1 < result.0.len() && i1 != j1 && 0 <= i2
                < result.0.len() && 0 <= j2 < result.0.len() && i2 != j2 && result.0[i1]
                + result.0[j1] == result.1 && result.0[i2] + result.0[j2] == result.1 ==> (i1
                == i2 && j1 == j2) || (i1 == j2 && j1 == i2),
{
    let n = if n < 2 { 2usize } else if n > 30000 { 30000usize } else { n };
    let a_val = if a_val < -1000 { -1000 } else if a_val > 498 { 498 } else { a_val };
    let low = if a_val + 3 > -1000 - a_val { a_val + 3 } else { -1000 - a_val };
    let high = if 1000 - a_val < 1000 { 1000 - a_val } else { 1000 };
    let b_val = if b_val < low { low } else if b_val > high { high } else { b_val };
    let target: i32 = a_val + b_val;

    if mutation_kind == 1u8 {
        // Mutation 1: two-element array [a_val, b_val]
        let mut nums: Vec<i32> = Vec::new();
        nums.push(a_val);
        nums.push(b_val);

        proof {
            assert(nums[0int] == a_val);
            assert(nums[1int] == b_val);
            assert(nums[0int] + nums[1int] == target);

            assert forall|i1: int, j1: int, i2: int, j2: int|
                0 <= i1 < nums.len() && 0 <= j1 < nums.len() && i1 != j1
                && 0 <= i2 < nums.len() && 0 <= j2 < nums.len() && i2 != j2
                && nums[i1] + nums[j1] == target && nums[i2] + nums[j2] == target
            implies (i1 == i2 && j1 == j2) || (i1 == j2 && j1 == i2)
            by {
                // Only indices 0 and 1 exist; only unordered pair is {0,1}
            }
        }

        let result = (nums, target);
        assert(result.0[0] + result.0[result.0.len() - 1] == result.1);
        result
    } else {
        // Mutation 0 (default): fillers = a_val + 1
        // Mutation 2: fillers = b_val - 1
        // Array: [a_val, f, f, ..., f, b_val]
        let f_val: i32 = if mutation_kind == 2u8 {
            (b_val - 1) as i32
        } else {
            (a_val + 1) as i32
        };

        proof {
            // Establish key arithmetic facts about f_val
            assert(a_val < f_val);
            assert(f_val < b_val);
            assert(-1_000 <= f_val && f_val <= 1_000);
        }

        let mut nums: Vec<i32> = Vec::new();
        nums.push(a_val);

        let mut i: usize = 1;
        while i < n - 1
            invariant
                2 <= n <= 30_000,
                1 <= i <= n - 1,
                nums.len() == i as int,
                nums[0int] == a_val,
                forall|k: int| 1 <= k < i as int ==> #[trigger] nums[k] == f_val,
                -1_000 <= a_val,
                b_val <= 1_000,
                b_val as int >= a_val as int + 3,
                a_val < f_val,
                f_val < b_val,
                -1_000 <= f_val && f_val <= 1_000,
            decreases n - 1 - i,
        {
            nums.push(f_val);
            i = i + 1;
        }

        nums.push(b_val);

        proof {
            assert(nums.len() == n as int);
            assert(nums[0int] == a_val);
            assert(nums[(n - 1) as int] == b_val);

            // All elements in bounds
            assert forall|k: int| 0 <= k < nums.len()
            implies -1_000 <= #[trigger] nums[k] <= 1_000
            by {
                if k == 0 {
                } else if k == nums.len() - 1 {
                } else {
                    assert(nums[k] == f_val);
                }
            }

            // Sortedness
            assert forall|k: int, l: int| 0 <= k < l < nums.len()
            implies nums[k] <= nums[l]
            by {
                if k == 0 {
                    if l == nums.len() - 1 {
                        assert(nums[k] == a_val && nums[l] == b_val);
                    } else {
                        assert(nums[k] == a_val && nums[l] == f_val);
                    }
                } else if l == nums.len() - 1 {
                    assert(nums[k] == f_val && nums[l] == b_val);
                } else {
                    assert(nums[k] == f_val && nums[l] == f_val);
                }
            }

            // Existence
            assert(nums[0int] + nums[(n - 1) as int] == target);

            // Uniqueness key facts
            assert(a_val as int + f_val as int != target as int);
            assert(f_val as int + b_val as int != target as int);
            assert(f_val as int + f_val as int != target as int);

            assert forall|i1: int, j1: int, i2: int, j2: int|
                0 <= i1 < nums.len() && 0 <= j1 < nums.len() && i1 != j1
                && 0 <= i2 < nums.len() && 0 <= j2 < nums.len() && i2 != j2
                && nums[i1] + nums[j1] == target && nums[i2] + nums[j2] == target
            implies (i1 == i2 && j1 == j2) || (i1 == j2 && j1 == i2)
            by {
                // Show (i1, j1) must be {0, n-1}
                if i1 == 0 {
                    if j1 != nums.len() - 1 {
                        if j1 > 0 {
                            assert(nums[j1] == f_val);
                            assert(a_val as int + f_val as int != target as int);
                        }
                    }
                } else if i1 == nums.len() - 1 {
                    if j1 != 0 {
                        if j1 != nums.len() - 1 {
                            assert(nums[j1] == f_val);
                            assert(b_val as int + f_val as int != target as int);
                        }
                    }
                } else {
                    assert(nums[i1] == f_val);
                    if j1 == 0 {
                        assert(f_val as int + a_val as int != target as int);
                    } else if j1 == nums.len() - 1 {
                        assert(f_val as int + b_val as int != target as int);
                    } else {
                        assert(nums[j1] == f_val);
                        assert(f_val as int + f_val as int != target as int);
                    }
                }
                // Show (i2, j2) must be {0, n-1}
                if i2 == 0 {
                    if j2 != nums.len() - 1 {
                        if j2 > 0 {
                            assert(nums[j2] == f_val);
                            assert(a_val as int + f_val as int != target as int);
                        }
                    }
                } else if i2 == nums.len() - 1 {
                    if j2 != 0 {
                        if j2 != nums.len() - 1 {
                            assert(nums[j2] == f_val);
                            assert(b_val as int + f_val as int != target as int);
                        }
                    }
                } else {
                    assert(nums[i2] == f_val);
                    if j2 == 0 {
                        assert(f_val as int + a_val as int != target as int);
                    } else if j2 == nums.len() - 1 {
                        assert(f_val as int + b_val as int != target as int);
                    } else {
                        assert(nums[j2] == f_val);
                        assert(f_val as int + f_val as int != target as int);
                    }
                }
            }
        }

        let result = (nums, target);
        assert(result.0[0] + result.0[result.0.len() - 1] == result.1);
        result
    }
}


pub fn example_case(which: u8) -> (result: (Vec<i32>, i32))
    ensures
        2 <= result.0.len() <= 30_000,
        -1_000 <= result.1 <= 1_000,
        forall|i: int|
            0 <= i < result.0.len() ==> -1_000 <= #[trigger] result.0[i] <= 1_000,
        forall |i: int, j: int|
            0 <= i < j < result.0.len() ==> result.0[i] <= result.0[j],
        exists|i: int, j: int|
            0 <= i < result.0.len() &&
            0 <= j < result.0.len() &&
            i != j &&
            result.0[i] + result.0[j] == result.1,
        forall|i1: int, j1: int, i2: int, j2: int|
            0 <= i1 < result.0.len() && 0 <= j1 < result.0.len() && i1 != j1 && 0 <= i2
                < result.0.len() && 0 <= j2 < result.0.len() && i2 != j2 && result.0[i1]
                + result.0[j1] == result.1 && result.0[i2] + result.0[j2] == result.1 ==> (i1
                == i2 && j1 == j2) || (i1 == j2 && j1 == i2),
{
    let mut nums: Vec<i32> = Vec::new();
    let target;
    if which == 0 {
        nums.push(2); nums.push(7); nums.push(11); nums.push(15); target = 9;
    } else if which == 1 {
        nums.push(2); nums.push(3); nums.push(4); target = 6;
    } else {
        nums.push(-1); nums.push(0); target = -1;
    }
    assert(nums[0] + nums[if which == 1 { 2int } else { 1int }] == target);
    (nums, target)
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

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

// Pick a valid (a_val, b_val, target) with a_val <= b_val, a+b == target in [-1000,1000],
// a+a != target, b+b != target.
fn pick_valid_pair(rng: &mut Rng, mode: usize) -> (i32, i32, i32) {
    loop {
        let (a, b) = match mode {
            0 => (-1000i32, rng.gen_range_i32(-1000, 1000)),
            1 => (rng.gen_range_i32(-1000, 1000), 1000i32),
            2 => (0i32, rng.gen_range_i32(-1000, 1000)),
            3 => {
                let x = rng.gen_range_i32(-500, 500);
                (-x, x)
            }
            4 => (-1i32, rng.gen_range_i32(-999, 1000)),
            5 => (rng.gen_range_i32(-1000, 0), rng.gen_range_i32(0, 1000)),
            6 => (rng.gen_range_i32(-1000, -1), rng.gen_range_i32(-1000, -1)),
            7 => (rng.gen_range_i32(1, 1000), rng.gen_range_i32(1, 1000)),
            8 => (-1000i32, 1000i32),
            9 => (rng.gen_range_i32(-500, 500), rng.gen_range_i32(-500, 500)),
            _ => (rng.gen_range_i32(-1000, 1000), rng.gen_range_i32(-1000, 1000)),
        };
        let (a, b) = if a <= b { (a, b) } else { (b, a) };
        let t64 = a as i64 + b as i64;
        if t64 < -1000 || t64 > 1000 {
            continue;
        }
        let target = t64 as i32;
        // a != b required for a+a != target (else 2a == a+b means a==b)
        if a == b {
            continue;
        }
        // a+a != target: 2a != a+b -> a != b: satisfied
        // b+b != target: 2b != a+b -> b != a: satisfied
        return (a, b, target);
    }
}

fn print_json(nums: &[i32], target: i32) {
    print!("{{\"numbers\":[");
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
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n: usize = 2;
        let idx_a: usize = 0;
        let idx_b: usize = 1;
        let (a, b, target) = pick_valid_pair(&mut rng, mode);
        let (nums, target) = generate_test_case(n, a, b, 1);
        print_json(&nums, target);
    }
}
