use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn all_ge_k(nums: Seq<i32>, k: int) -> bool {
        forall |i: int| 0 <= i < nums.len() ==> nums[i] as int >= k
    }

    pub open spec fn count_lt_prefix(nums: Seq<i32>, k: int, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::count_lt_prefix(nums, k, end - 1)
                + if (nums[end - 1] as int) < k { 1int } else { 0int }
        }
    }

    pub open spec fn count_lt_k(nums: Seq<i32>, k: int) -> int {
        Self::count_lt_prefix(nums, k, nums.len() as int)
    }

    pub open spec fn min_operations_spec(nums: Seq<i32>, k: int, res: int) -> bool {
        &&& 2 <= nums.len() <= 200_000
        &&& 1 <= k <= 1_000_000_000
        &&& forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000
        &&& 0 <= res < nums.len()
        &&& (Self::all_ge_k(nums, k) <==> res == 0)
        &&& (Self::count_lt_k(nums, k) == 1 ==> res == 1)
        &&& res <= Self::count_lt_k(nums, k)
    }

    pub fn min_operations_model(nums: Vec<i32>, k: i32) -> (res: i32)
        requires
            2 <= nums.len() <= 200_000,
            1 <= k <= 1_000_000_000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
    {
        let mut heap: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < nums.len() {
            Self::heap_push(&mut heap, nums[i] as i64);
            i = i + 1;
        }

        let kk = k as i64;
        let mut ops: i32 = 0;
        let mut steps_left: usize = nums.len() - 1;
        while heap.len() > 1 && heap[0] < kk && steps_left > 0
        {
            let x = Self::heap_pop_min(&mut heap);
            let y = Self::heap_pop_min(&mut heap);

            let doubled_opt = x.checked_mul(2);
            let mut doubled = i64::MAX;
            if doubled_opt.is_some() {
                doubled = doubled_opt.unwrap();
            }

            let combined_opt = doubled.checked_add(y);
            let mut combined = i64::MAX;
            if combined_opt.is_some() {
                combined = combined_opt.unwrap();
            }

            Self::heap_push(&mut heap, combined);
            ops = ops + 1;
            steps_left = steps_left - 1;
        }
        ops
    }

    fn heap_push(heap: &mut Vec<i64>, val: i64) {
        heap.push(val);
        let mut child = heap.len() - 1;
        while child > 0
            decreases child,
        {
            let parent = (child - 1) / 2;
            if heap[parent] <= heap[child] {
                break;
            }
            let tmp = heap[parent];
            heap.set(parent, heap[child]);
            heap.set(child, tmp);
            child = parent;
        }
    }

    fn heap_pop_min(heap: &mut Vec<i64>) -> i64 {
        let mut min_val: i64 = 0;
        if heap.len() == 0 {
            return min_val;
        }
        min_val = heap[0];
        let last_opt = heap.pop();
        let mut last = min_val;
        if last_opt.is_some() {
            last = last_opt.unwrap();
        }
        if heap.len() > 0 {
            heap.set(0, last);
            let mut i: usize = 0;
            while i < heap.len() / 2
            {
                let left = i * 2 + 1;
                let right = left + 1;
                let mut smallest = left;
                if right < heap.len() && heap[right] < heap[left] {
                    smallest = right;
                }
                if heap[i] <= heap[smallest] {
                    break;
                }
                let tmp = heap[i];
                heap.set(i, heap[smallest]);
                heap.set(smallest, tmp);
                i = smallest;
            }
        }
        min_val
    }

    pub fn min_operations(nums: Vec<i32>, k: i32) -> (res: i32)
        requires
            2 <= nums.len() <= 200_000,
            1 <= k <= 1_000_000_000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            Self::min_operations_spec(nums@, k as int, res as int),
    {
        let mut all_ge = true;
        let mut initial_lt: i32 = 0;
        let mut t: usize = 0;
        while t < nums.len()
        {
            if nums[t] < k {
                all_ge = false;
                initial_lt = initial_lt + 1;
            }
            t = t + 1;
        }
        if all_ge {
            return 0;
        }

        let mut heap: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < nums.len()
        {
            Self::heap_push(&mut heap, nums[i] as i64);
            i = i + 1;
        }

        let kk = k as i64;
        let mut ops: i32 = 0;
        let mut steps_left: usize = nums.len() - 1;
        while heap.len() > 1 && heap[0] < kk && steps_left > 0 && ops < initial_lt
        {
            let x = Self::heap_pop_min(&mut heap);
            let y = Self::heap_pop_min(&mut heap);

            let doubled_opt = x.checked_mul(2);
            let mut doubled = i64::MAX;
            if doubled_opt.is_some() {
                doubled = doubled_opt.unwrap();
            }

            let combined_opt = doubled.checked_add(y);
            let mut combined = i64::MAX;
            if combined_opt.is_some() {
                combined = combined_opt.unwrap();
            }

            Self::heap_push(&mut heap, combined);
            ops = ops + 1;
            steps_left = steps_left - 1;
        }
        if ops == 0 {
            1
        } else {
            ops
        }
    }
}

}
