use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    fillers: Vec<i32>,
    max_val: i32,
    max_idx: usize,
    mutation_kind: u8,
) -> (result: Vec<i32>)
    requires
        1 <= fillers.len() <= 49,
        0 <= max_val <= 100,
        forall|i: int| 0 <= i < fillers.len() ==> 0 <= #[trigger] fillers[i] <= 100,
        forall|i: int| 0 <= i < fillers.len() ==> fillers[i] < max_val,
        0 <= max_idx <= fillers.len(),
    ensures
        2 <= result.len() <= 50,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 100,
        exists|i: int| #![trigger result[i]] 0 <= i < result.len() &&
            forall|j: int| 0 <= j < result.len() && j != i ==> result[i] > #[trigger] result[j],
{
    assert(fillers[0] < max_val);
    assert(fillers[0] >= 0i32);

    let mut nums: Vec<i32> = Vec::new();
    let mut k: usize = 0;

    while k < max_idx
        invariant
            0 <= k <= max_idx,
            max_idx <= fillers.len(),
            nums.len() == k,
            forall|i: int| 0 <= i < k ==> nums[i] == fillers[i],
            forall|i: int| 0 <= i < k ==> 0 <= #[trigger] nums[i] <= 100,
            forall|i: int| 0 <= i < k ==> nums[i] < max_val,
            1 <= fillers.len() <= 49,
            0 <= max_val <= 100,
            forall|i: int| 0 <= i < fillers.len() ==> 0 <= #[trigger] fillers[i] <= 100,
            forall|i: int| 0 <= i < fillers.len() ==> fillers[i] < max_val,
        decreases max_idx - k,
    {
        nums.push(fillers[k]);
        k += 1;
    }

    nums.push(max_val);

    let mut k2: usize = max_idx;
    while k2 < fillers.len()
        invariant
            max_idx <= k2 <= fillers.len(),
            nums.len() == k2 + 1,
            nums[max_idx as int] == max_val,
            forall|i: int| 0 <= i < max_idx ==> nums[i] == fillers[i],
            forall|i: int| (max_idx + 1) as int <= i < nums.len() ==> nums[i] == fillers[i - 1],
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 100,
            forall|i: int| 0 <= i < nums.len() && i != max_idx as int ==> nums[i] < max_val,
            1 <= fillers.len() <= 49,
            0 <= max_val <= 100,
            forall|i: int| 0 <= i < fillers.len() ==> 0 <= #[trigger] fillers[i] <= 100,
            forall|i: int| 0 <= i < fillers.len() ==> fillers[i] < max_val,
        decreases fillers.len() - k2,
    {
        nums.push(fillers[k2]);
        k2 += 1;
    }

    assert(nums.len() == fillers.len() + 1);
    assert(2 <= nums.len() <= 50);
    assert(nums[max_idx as int] == max_val);
    assert forall|j: int| 0 <= j < nums.len() && j != max_idx as int
        implies nums[max_idx as int] > #[trigger] nums[j] by {}

    if mutation_kind == 0 {
        nums
    } else if mutation_kind == 1 {
        let mut m: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < nums.len()
            invariant
                0 <= i <= nums.len(),
                m.len() == i,
                2 <= nums.len() <= 50,
                1 <= max_val <= 100,
                max_idx < nums.len(),
                forall|j: int| 0 <= j < i ==> 0 <= #[trigger] m[j] <= 100,
                forall|j: int| 0 <= j < i && j != max_idx as int ==> m[j] == 0i32,
                i > max_idx as usize ==> m[max_idx as int] == max_val,
            decreases nums.len() - i,
        {
            if i == max_idx {
                m.push(max_val);
            } else {
                m.push(0);
            }
            i += 1;
        }
        assert(m.len() == nums.len());
        assert(m[max_idx as int] == max_val);
        assert forall|j: int| 0 <= j < m.len() && j != max_idx as int
            implies m[max_idx as int] > #[trigger] m[j] by {
            assert(m[j] == 0i32);
        }
        m
    } else if mutation_kind == 2 {
        let fill_val: i32 = max_val - 1;
        let mut m: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < nums.len()
            invariant
                0 <= i <= nums.len(),
                m.len() == i,
                2 <= nums.len() <= 50,
                1 <= max_val <= 100,
                fill_val == max_val - 1,
                0 <= fill_val <= 99,
                max_idx < nums.len(),
                forall|j: int| 0 <= j < i ==> 0 <= #[trigger] m[j] <= 100,
                forall|j: int| 0 <= j < i && j != max_idx as int ==> m[j] == fill_val,
                i > max_idx as usize ==> m[max_idx as int] == max_val,
            decreases nums.len() - i,
        {
            if i == max_idx {
                m.push(max_val);
            } else {
                m.push(fill_val);
            }
            i += 1;
        }
        assert(m.len() == nums.len());
        assert(m[max_idx as int] == max_val);
        assert forall|j: int| 0 <= j < m.len() && j != max_idx as int
            implies m[max_idx as int] > #[trigger] m[j] by {
            assert(m[j] == fill_val);
        }
        m
    } else if mutation_kind == 3 && max_idx > 0 {
        let old_first = nums[0];
        nums.set(0, max_val);
        nums.set(max_idx, old_first);
        assert(nums[0] == max_val);
        assert forall|j: int| 0 <= j < nums.len() && j != 0
            implies nums[0] > #[trigger] nums[j] by {}
        nums
    } else if mutation_kind == 4 && max_idx < nums.len() - 1 {
        let last = nums.len() - 1;
        let old_last = nums[last];
        nums.set(last, max_val);
        nums.set(max_idx, old_last);
        assert(nums[last as int] == max_val);
        assert forall|j: int| 0 <= j < nums.len() && j != last as int
            implies nums[last as int] > #[trigger] nums[j] by {}
        nums
    } else {
        nums
    }
}

} // verus!

extern crate serde_json;
use serde_json::json;

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn make_test(fillers: Vec<i32>, max_val: i32, max_idx: usize, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(fillers, max_val, max_idx, mutation_kind)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    use std::io::Write;

    let mut generated: usize = 0;

    // Example 1: nums = [3,6,1,0] — fillers=[3,1,0], max_val=6, max_idx=1
    {
        let nums = make_test(vec![3, 1, 0], 6, 1, 0);
        let result = Solution::dominant_index(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": result})).unwrap();
        generated += 1;
    }

    // Example 2: nums = [1,2,3,4] — fillers=[1,2,3], max_val=4, max_idx=3
    {
        let nums = make_test(vec![1, 2, 3], 4, 3, 0);
        let result = Solution::dominant_index(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": result})).unwrap();
        generated += 1;
    }

    // Edge: two elements, dominant — fillers=[0], max_val=100, max_idx=1
    {
        let nums = make_test(vec![0], 100, 1, 0);
        let result = Solution::dominant_index(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": result})).unwrap();
        generated += 1;
    }

    // Edge: two elements, not dominant — fillers=[49], max_val=50, max_idx=1
    {
        let nums = make_test(vec![49], 50, 1, 0);
        let result = Solution::dominant_index(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": result})).unwrap();
        generated += 1;
    }

    // Edge: max at first position — fillers=[1,2,3], max_val=100, max_idx=0
    {
        let nums = make_test(vec![1, 2, 3], 100, 0, 0);
        let result = Solution::dominant_index(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": result})).unwrap();
        generated += 1;
    }

    // Edge: max at last position — fillers=[1,2,3], max_val=100, max_idx=3
    {
        let nums = make_test(vec![1, 2, 3], 100, 3, 0);
        let result = Solution::dominant_index(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": result})).unwrap();
        generated += 1;
    }

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4];

    let mut _attempts: usize = 0;
    while generated < count {
        _attempts += 1;
        if _attempts > 10000 { break; }

        let n: usize = match generated % 5 {
            0 => rng.gen_range_usize(2, 3),
            1 => rng.gen_range_usize(2, 5),
            2 => rng.gen_range_usize(6, 15),
            3 => rng.gen_range_usize(16, 35),
            _ => rng.gen_range_usize(36, 50),
        };

        let max_val: i32 = match generated % 10 {
            0 => 1,
            1 => 2,
            2 => 100,
            3 => 99,
            4 => 50,
            _ => rng.gen_range_i64(1, 100) as i32,
        };

        let filler_count = n - 1;
        let mut fillers: Vec<i32> = Vec::with_capacity(filler_count);
        for _ in 0..filler_count {
            let v = if max_val == 1 {
                0
            } else {
                rng.gen_range_i64(0, (max_val - 1) as i64) as i32
            };
            fillers.push(v);
        }

        let max_idx = rng.gen_range_usize(0, filler_count);
        let mk = mutation_kinds[generated % mutation_kinds.len()];

        let nums = make_test(fillers, max_val, max_idx, mk);
        let result = Solution::dominant_index(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": result})).unwrap();
        generated += 1;
    }

    eprintln!("Generated {} test cases to {:?}", generated, out_path);
}
