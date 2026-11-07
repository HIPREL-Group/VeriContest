impl Solution {
    pub fn result_array(nums: Vec<i32>) -> Vec<i32> {
        let n = nums.len();
        let mut arr1: Vec<i32> = Vec::new();
        let mut arr2: Vec<i32> = Vec::new();
        arr1.push(nums[0]);
        arr2.push(nums[1]);
        let mut i: usize = 2;
        while i < n {
            if arr1[arr1.len() - 1] > arr2[arr2.len() - 1] {
                arr1.push(nums[i]);
            } else {
                arr2.push(nums[i]);
            }
            i = i + 1;
        }
        let mut result = arr1;
        let mut j: usize = 0;
        while j < arr2.len() {
            result.push(arr2[j]);
            j = j + 1;
        }
        result
    }
}
