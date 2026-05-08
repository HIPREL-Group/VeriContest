impl Solution {
    pub fn max_turbulence_size(arr: Vec<i32>) -> i32 {
        let n = arr.len();
        let mut best: usize = 1;
        let mut cur: usize = 1;
        let mut i: usize = 1;

        while i < n {
            if i >= 2
                && ((arr[i - 2] < arr[i - 1] && arr[i - 1] > arr[i])
                    || (arr[i - 2] > arr[i - 1] && arr[i - 1] < arr[i]))
            {
                cur = cur + 1;
            } else if arr[i - 1] != arr[i] {
                cur = 2;
            } else {
                cur = 1;
            }

            if cur > best {
                best = cur;
            }

            i = i + 1;
        }

        best as i32
    }
}
