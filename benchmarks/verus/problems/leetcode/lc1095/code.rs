pub struct MountainArray {
    pub data: Vec<i32>,
}

impl MountainArray {
    pub fn get(&self, index: i32) -> i32 {
        self.data[index as usize]
    }

    pub fn length(&self) -> i32 {
        self.data.len() as i32
    }
}

impl Solution {
    pub fn find_in_mountain_array(target: i32, mountain_arr: &MountainArray) -> i32 {
        let n = mountain_arr.length();
        let mut left: i32 = 0;
        let mut right: i32 = n - 1;
        while left < right {
            let mid = left + (right - left) / 2;
            if mountain_arr.get(mid) < mountain_arr.get(mid + 1) {
                left = mid + 1;
            } else {
                right = mid;
            }
        }
        let peak = left;
        let mut lo: i32 = 0;
        let mut hi: i32 = peak + 1;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if mountain_arr.get(mid) < target {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        if lo <= peak && mountain_arr.get(lo) == target {
            return lo;
        }
        lo = peak + 1;
        hi = n;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if mountain_arr.get(mid) > target {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        if lo < n && mountain_arr.get(lo) == target {
            return lo;
        }
        -1
    }
}
