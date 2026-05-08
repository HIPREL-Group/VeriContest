impl Solution {
    fn heap_push(heap: &mut Vec<i64>, val: i64) {
        heap.push(val);
        let mut child = heap.len() - 1;
        while child > 0 {
            let parent = (child - 1) / 2;
            if heap[parent] <= heap[child] {
                break;
            }
            let tmp = heap[parent];
            heap[parent] = heap[child];
            heap[child] = tmp;
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
            heap[0] = last;
            let mut i: usize = 0;
            while i < heap.len() / 2 {
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
                heap[i] = heap[smallest];
                heap[smallest] = tmp;
                i = smallest;
            }
        }
        min_val
    }

    pub fn min_operations(nums: Vec<i32>, k: i32) -> i32 {
        let mut all_ge = true;
        let mut initial_lt: i32 = 0;
        let mut t: usize = 0;
        while t < nums.len() {
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
        while i < nums.len() {
            Self::heap_push(&mut heap, nums[i] as i64);
            i = i + 1;
        }

        let kk = k as i64;
        let mut ops: i32 = 0;
        let mut steps_left: usize = nums.len() - 1;
        while heap.len() > 1 && heap[0] < kk && steps_left > 0 && ops < initial_lt {
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
}
