use vstd::prelude::*;

verus! {

spec fn fill_val(k: int, d: int) -> int {
    if k - 1 < d { k - 1 } else { k }
}

pub fn generate_test_case(
    n: usize,
    dup_val: i32,
    mutation_kind: u8,
) -> (nums: Vec<i32>)
    requires
        1 <= n <= 100_000,
        1 <= dup_val <= n,
    ensures
        1 <= nums.len() - 1 <= 100_000,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= nums.len() - 1,
        exists |i: int, j: int| 0 <= i < j < nums.len() && nums[i] == nums[j],
        forall |i1: int, j1: int, i2: int, j2: int|
            0 <= i1 < j1 < nums.len() &&
            0 <= i2 < j2 < nums.len() &&
            nums[i1] == nums[j1] &&
            nums[i2] == nums[j2] ==> nums[i1] == nums[i2],
{
    let mut nums: Vec<i32> = Vec::new();
    nums.push(dup_val);
    nums.push(dup_val);

    let mut k: usize = 2;
    while k <= n
        invariant
            2 <= k <= n + 1,
            nums.len() == k,
            1 <= n <= 100_000,
            1 <= dup_val <= n,
            nums[0int] == dup_val,
            nums[1int] == dup_val,
            forall |j: int| 2 <= j < k as int ==>
                #[trigger] nums[j] == fill_val(j, dup_val as int),
            forall |j: int| 0 <= j < k as int ==>
                1 <= #[trigger] nums[j] <= n as int,
        decreases n + 1 - k,
    {
        let val: i32 = if k - 1 < dup_val as usize {
            (k - 1) as i32
        } else {
            k as i32
        };
        assert(val == fill_val(k as int, dup_val as int));
        assert(1 <= val <= n as i32) by {
            if (k as int - 1) < dup_val as int {
                assert(val as int == k as int - 1);
            } else {
                assert(val as int == k as int);
            }
        };
        nums.push(val);
        k = k + 1;
    }

    if mutation_kind == 1u8 && n >= 2 {
        let last_val = nums[n];
        let first_val = nums[0usize];
        nums.set(0, last_val);
        nums.set(n, first_val);
    }

    proof {
        assert(nums.len() == n + 1);
        assert(1 <= nums.len() - 1 <= 100_000);

        assert forall |j: int| 2 <= j <= n as int
            implies #[trigger] fill_val(j, dup_val as int) != dup_val as int
        by {
            if j - 1 < dup_val as int {
                assert(fill_val(j, dup_val as int) == j - 1);
            } else {
                assert(fill_val(j, dup_val as int) == j);
            }
        }

        assert forall |j1: int, j2: int|
            2 <= j1 <= n as int && 2 <= j2 <= n as int && j1 != j2
            implies #[trigger] fill_val(j1, dup_val as int) != #[trigger] fill_val(j2, dup_val as int)
        by {
            if j1 - 1 < dup_val as int && j2 - 1 < dup_val as int {
            } else if j1 - 1 >= dup_val as int && j2 - 1 >= dup_val as int {
            } else if j1 - 1 < dup_val as int && j2 - 1 >= dup_val as int {
                assert(fill_val(j1, dup_val as int) == j1 - 1);
                assert(fill_val(j2, dup_val as int) == j2);
            } else {
                assert(fill_val(j2, dup_val as int) == j2 - 1);
                assert(fill_val(j1, dup_val as int) == j1);
            }
        }

        if mutation_kind == 1u8 && n >= 2 {
            assert(nums[1int] == dup_val);
            assert(nums[n as int] == dup_val);
            assert(1int < n as int);

            assert forall |i: int| 0 <= i < nums.len()
                implies 1 <= #[trigger] nums[i] <= nums.len() - 1
            by {
                if i == 0 {
                    assert(nums[i] == fill_val(n as int, dup_val as int));
                } else if i == n as int {
                    assert(nums[i] == dup_val);
                } else if i == 1 {
                    assert(nums[i] == dup_val);
                } else {
                    assert(nums[i] == fill_val(i, dup_val as int));
                }
            }

            assert forall |i1: int, j1: int, i2: int, j2: int|
                0 <= i1 < j1 < nums.len() &&
                0 <= i2 < j2 < nums.len() &&
                #[trigger] nums[i1] == #[trigger] nums[j1] &&
                #[trigger] nums[i2] == #[trigger] nums[j2]
                implies nums[i1] == nums[i2]
            by {
                if i1 == 1 || i1 == n as int {
                    assert(nums[i1] == dup_val);
                    if i2 == 1 || i2 == n as int {
                        assert(nums[i2] == dup_val);
                    } else if j2 == 1 || j2 == n as int {
                        assert(nums[j2] == dup_val);
                        if i2 == 0 {
                            assert(nums[i2] == fill_val(n as int, dup_val as int));
                        } else {
                            assert(nums[i2] == fill_val(i2, dup_val as int));
                        }
                    } else {
                        let fi2 = if i2 == 0 { n as int } else { i2 };
                        let fj2 = if j2 == 0 { n as int } else { j2 };
                        if i2 == 0 {
                            assert(nums[i2] == fill_val(n as int, dup_val as int));
                        } else {
                            assert(nums[i2] == fill_val(i2, dup_val as int));
                        }
                        if j2 == 0 {
                            assert(nums[j2] == fill_val(n as int, dup_val as int));
                        } else {
                            assert(nums[j2] == fill_val(j2, dup_val as int));
                        }
                        assert(fi2 != fj2);
                    }
                } else if j1 == 1 || j1 == n as int {
                    assert(nums[j1] == dup_val);
                    if i1 == 0 {
                        assert(nums[i1] == fill_val(n as int, dup_val as int));
                    } else {
                        assert(nums[i1] == fill_val(i1, dup_val as int));
                    }
                } else {
                    let fi1 = if i1 == 0 { n as int } else { i1 };
                    let fj1 = if j1 == 0 { n as int } else { j1 };
                    if i1 == 0 {
                        assert(nums[i1] == fill_val(n as int, dup_val as int));
                    } else {
                        assert(nums[i1] == fill_val(i1, dup_val as int));
                    }
                    if j1 == 0 {
                        assert(nums[j1] == fill_val(n as int, dup_val as int));
                    } else {
                        assert(nums[j1] == fill_val(j1, dup_val as int));
                    }
                    assert(fi1 != fj1);
                }
            }
        } else {
            assert(nums[0int] == dup_val);
            assert(nums[1int] == dup_val);

            assert forall |i: int| 0 <= i < nums.len()
                implies 1 <= #[trigger] nums[i] <= nums.len() - 1
            by {
                if i <= 1 {
                    assert(nums[i] == dup_val);
                } else {
                    assert(nums[i] == fill_val(i, dup_val as int));
                }
            }

            assert forall |i1: int, j1: int, i2: int, j2: int|
                0 <= i1 < j1 < nums.len() &&
                0 <= i2 < j2 < nums.len() &&
                #[trigger] nums[i1] == #[trigger] nums[j1] &&
                #[trigger] nums[i2] == #[trigger] nums[j2]
                implies nums[i1] == nums[i2]
            by {
                if i1 <= 1 {
                    assert(nums[i1] == dup_val);
                    if i2 <= 1 {
                        assert(nums[i2] == dup_val);
                    } else if j2 <= 1 {
                    } else {
                        assert(nums[i2] == fill_val(i2, dup_val as int));
                        assert(nums[j2] == fill_val(j2, dup_val as int));
                        assert(i2 != j2);
                    }
                } else if j1 <= 1 {
                } else {
                    assert(nums[i1] == fill_val(i1, dup_val as int));
                    assert(nums[j1] == fill_val(j1, dup_val as int));
                    assert(i1 != j1);
                }
            }
        }
    }

    nums
}

} // verus!

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

extern crate serde_json;
use serde_json::json;

struct Solution;
include!("../code.rs");

fn main() {
    use std::io::Write;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);

    let mut rng = Rng::new(seed);
    let mut generated = 0usize;

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 3, 4, 2, 2],
        vec![3, 1, 3, 4, 2],
        vec![3, 3, 3, 3, 3],
    ];
    for nums in &examples {
        if generated >= count { break; }
        let nums_clone = nums.clone();
        let result = Solution::find_duplicate(nums_clone);
        writeln!(out, "{}", json!({
            "input": { "nums": nums },
            "output": result
        })).unwrap();
        generated += 1;
    }

    while generated < count {
        let n: usize = match generated % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 10000),
        };

        let dup_val: i32 = if generated % 5 == 0 {
            match rng.gen_range_usize(0, 2) {
                0 => 1,
                1 => n as i32,
                _ => (n as i32 + 1) / 2,
            }
        } else {
            rng.gen_range_i64(1, n as i64) as i32
        };

        let mutation_kind: u8 = if n >= 2 {
            rng.gen_range_usize(0, 1) as u8
        } else {
            0
        };

        let nums = generate_test_case(n, dup_val, mutation_kind);
        let nums_plain: Vec<i32> = nums.iter().map(|&x| x).collect();
        let result = Solution::find_duplicate(nums_plain.clone());

        writeln!(out, "{}", json!({
            "input": { "nums": nums_plain },
            "output": result
        })).unwrap();

        generated += 1;
    }

    eprintln!("Generated {} test cases to {:?}", generated, out_path);
}
