pub struct MajorityChecker {
    pub arr: Vec<i32>,
}

impl MajorityChecker {
    pub fn new(arr: Vec<i32>) -> Self {
        MajorityChecker { arr }
    }

    pub fn query(&self, left: i32, right: i32, threshold: i32) -> i32 {
        let l = left as usize;
        let r = right as usize;
        let mut candidate: i32 = self.arr[l];
        let mut cnt: i32 = 0;
        let mut i: usize = l;
        while i <= r {
            if cnt == 0 {
                candidate = self.arr[i];
                cnt = 1;
            } else if self.arr[i] == candidate {
                cnt = cnt + 1;
            } else {
                cnt = cnt - 1;
            }
            i = i + 1;
        }
        let mut actual_count: i32 = 0;
        let mut j: usize = l;
        while j <= r {
            if self.arr[j] == candidate {
                actual_count = actual_count + 1;
            }
            j = j + 1;
        }
        if actual_count >= threshold {
            candidate
        } else {
            -1
        }
    }
}
