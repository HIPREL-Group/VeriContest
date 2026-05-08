impl Solution {
    pub fn find_the_distance_value(arr1: Vec<i32>, arr2: Vec<i32>, d: i32) -> i32 {
        let mut result: i32 = 0;
        let mut i: usize = 0;
        while i < arr1.len() {
            let x = arr1[i];
            let mut ok: bool = true;
            let mut j: usize = 0;
            while j < arr2.len() {
                let diff = x as i64 - arr2[j] as i64;
                let abs_diff = if diff < 0 { -diff } else { diff };
                if abs_diff <= d as i64 {
                    ok = false;
                }
                j = j + 1;
            }
            if ok {
                result = result + 1;
            }
            i = i + 1;
        }
        result
    }
}
