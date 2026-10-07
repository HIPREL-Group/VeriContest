use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    key: i32,
    key_pos: usize,
    fillers: &Vec<i32>,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= key <= 1000,
        fillers.len() + 1 >= 2,
        fillers.len() + 1 <= 1000,
        key_pos < fillers.len(),
        forall|ii: int| 0 <= ii < fillers.len() as int ==> 1 <= #[trigger] fillers[ii] <= 1000,
    ensures
        2 <= result.0.len() <= 1000,
        1 <= result.1 <= 1000,
        result.1 == key,
        result.0.len() == fillers.len() + 1,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1000,
        exists|i: int| 0 <= i < result.0.len() - 1 && result.0[i] == key,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < key_pos
        invariant
            i <= key_pos,
            key_pos < fillers.len(),
            nums.len() == i,
            forall|k: int| 0 <= k < fillers.len() as int ==> 1 <= #[trigger] fillers[k] <= 1000,
            forall|j: int| 0 <= j < i as int ==> nums@[j] == #[trigger] fillers[j],
            forall|j: int| 0 <= j < i as int ==> 1 <= #[trigger] nums@[j] <= 1000,
        decreases key_pos - i,
    {
        let ghost s_pre = nums@;
        nums.push(fillers[i]);
        proof {
            assert(nums@ == s_pre.push(fillers[i as int]));
            assert forall|j: int| 0 <= j < (i + 1) as int implies #[trigger] nums@[j] == fillers[j] by {
                if j < i as int {
                    assert(nums@[j] == s_pre[j]);
                    assert(s_pre[j] == fillers[j]);
                } else {
                    assert(j == i as int);
                    assert(nums@[j] == fillers[i as int]);
                    assert(s_pre.push(fillers[i as int])[j] == fillers[i as int]);
                }
            };
            assert forall|j: int| 0 <= j < (i + 1) as int implies 1 <= #[trigger] nums@[j] <= 1000 by {
                if j < i as int {
                    assert(1 <= nums@[j] <= 1000);
                } else {
                    assert(j == i as int);
                    assert(1 <= fillers[i as int] <= 1000);
                    assert(nums@[j] == fillers[i as int]);
                }
            };
        }
        i = i + 1;
    }
    nums.push(key);
    assert(i == key_pos);
    assert(nums.len() == i + 1);
    assert(nums@[key_pos as int] == key);

    while i < fillers.len()
        invariant
            key_pos <= i,
            i <= fillers.len(),
            nums.len() == i + 1,
            nums@[key_pos as int] == key,
            forall|k: int| 0 <= k < fillers.len() as int ==> 1 <= #[trigger] fillers[k] <= 1000,
            forall|j: int| 0 <= j < key_pos as int ==> nums@[j] == #[trigger] fillers[j],
            forall|j: int| key_pos < j < nums.len() as int ==> nums@[j] == #[trigger] fillers[j - 1],
            forall|j: int| 0 <= j < nums.len() as int ==> 1 <= #[trigger] nums@[j] <= 1000,
        decreases fillers.len() - i,
    {
        let ghost s_pre = nums@;
        nums.push(fillers[i]);
        proof {
            assert(nums@ == s_pre.push(fillers[i as int]));
            assert(nums@[key_pos as int] == key);
            assert forall|j: int| key_pos < j < nums.len() as int implies nums@[j] == fillers[j - 1] by {
                if j < s_pre.len() as int {
                    assert(nums@[j] == s_pre[j]);
                    assert(s_pre[j] == fillers[j - 1]);
                } else {
                    assert(j == s_pre.len() as int);
                    assert(nums@[j] == fillers[i as int]);
                    assert(j - 1 == i as int);
                    assert(nums@[j] == fillers[j - 1]);
                }
            };
            assert forall|j: int| 0 <= j < nums.len() as int implies 1 <= #[trigger] nums@[j] <= 1000 by {
                if j < s_pre.len() as int {
                    assert(1 <= nums@[j] <= 1000);
                } else {
                    assert(j == s_pre.len() as int);
                    assert(1 <= fillers[i as int] <= 1000);
                    assert(nums@[j] == fillers[i as int]);
                }
            };
        }
        i = i + 1;
    }

    proof {
        assert(nums.len() == fillers.len() + 1);
        assert(0 <= key_pos as int);
        assert((key_pos as int) < nums.len() as int - 1);
        assert(nums@[key_pos as int] == key);
    }

    (nums, key)
}

} // verus!

struct Solution;
include!("../code.rs");

fn follow_count(nums: &[i32], key: i32, target: i32) -> usize {
    let mut c = 0usize;
    let n = nums.len();
    if n < 2 {
        return 0;
    }
    for i in 0..n - 1 {
        if nums[i] == key && nums[i + 1] == target {
            c += 1;
        }
    }
    c
}

fn unique_max_follow_key(nums: &[i32], key: i32) -> bool {
    let mut max_c = 0usize;
    for t in 1i32..=1000 {
        let c = follow_count(nums, key, t);
        if c > max_c {
            max_c = c;
        }
    }
    let mut n_at_max = 0usize;
    for t in 1i32..=1000 {
        if follow_count(nums, key, t) == max_c {
            n_at_max += 1;
        }
    }
    n_at_max == 1
}

/// Extends `nums` so the follow-count for `key` has a unique maximizer (spec precondition).
fn repair_for_unique_max(nums: &mut Vec<i32>, key: i32) -> bool {
    let mut guard = 0usize;
    while !unique_max_follow_key(nums, key) {
        guard += 1;
        if guard > 20 {
            return false;
        }
        if nums.len() >= 1000 {
            return false;
        }
        let w = Solution::most_frequent(nums.clone(), key);
        match nums.last() {
            Some(&last) if last == key => nums.push(w),
            Some(_) => {
                if nums.len() + 2 > 1000 {
                    return false;
                }
                nums.push(key);
                nums.push(w);
            }
            None => return false,
        }
    }
    true
}

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

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn make_fillers(rng: &mut Rng, count: usize, mode: usize, key: i32) -> Vec<i32> {
    let mut res: Vec<i32> = Vec::with_capacity(count);
    for i in 0..count {
        let v = match mode {
            0 => rng.gen_range_i32(1, 1000),
            1 => key,
            2 => {
                // mostly key, few others
                if rng.next_u64() % 3 == 0 {
                    rng.gen_range_i32(1, 1000)
                } else {
                    key
                }
            }
            3 => 1,
            4 => 1000,
            5 => {
                // alternating
                if i % 2 == 0 { key } else { rng.gen_range_i32(1, 1000) }
            }
            6 => {
                if key < 1000 { key + 1 } else { key - 1 }
            }
            7 => {
                // two target candidates after key
                if i % 2 == 0 {
                    100
                } else {
                    200
                }
            }
            8 => {
                // pairs (key, x) scattered
                if i % 3 == 0 { key } else { rng.gen_range_i32(1, 10) }
            }
            _ => rng.gen_range_i32(1, 5),
        };
        let v = if v < 1 { 1 } else if v > 1000 { 1000 } else { v };
        res.push(v);
    }
    res
}

/// Same JSONL shape as `gen.rs`: every line is a checkable harness case with golden `output`.
fn testcase_json_line(nums: &[i32], key: i32, output: i32) -> String {
    format!(r#"{{"input":{{"nums":{:?},"key":{}}},"output":{}}}"#, nums, key, output)
}

fn main() {
    use std::io::Write;

    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };
    let total: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(220);

    let mut rng = Rng::new(seed);
    let modes = 10usize;

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);

    let mut emitted = 0usize;
    for attempt in 0..(total * 200) {
        if emitted >= total {
            break;
        }
        let mode = attempt % modes;
        let mut n: usize = match mode {
            0 => 2 + (attempt % 10),
            1 => 1000,
            2 => 17,
            3 => if attempt % 2 == 0 { 2 } else { 256 },
            4 => 3 + (attempt % 7),
            5 => 64,
            6 => 500,
            7 => 997,
            8 => 1000,
            _ => 50 + (attempt % 100),
        };
        // Leave slack for `repair_for_unique_max` (up to two appends).
        if n > 998 {
            n = 998;
        }

        let key: i32 = match mode {
            0 => rng.gen_range_i32(1, 1000),
            1 => 1,
            2 => 1000,
            3 => rng.gen_range_i32(1, 10),
            4 => 500,
            5 => rng.gen_range_i32(1, 1000),
            6 => 2,
            7 => rng.gen_range_i32(1, 1000),
            8 => 1,
            _ => rng.gen_range_i32(1, 1000),
        };

        let fillers_len = n - 1;
        let fillers = make_fillers(&mut rng, fillers_len, mode, key);
        let key_pos = rng.gen_range_usize(0, fillers_len - 1);

        let (mut nums, k) = generate_test_case(key, key_pos, &fillers);
        if !repair_for_unique_max(&mut nums, k) {
            continue;
        }
        let output = Solution::most_frequent(nums.clone(), k);
        writeln!(out, "{}", testcase_json_line(&nums, k, output)).unwrap();
        emitted += 1;
    }
}
