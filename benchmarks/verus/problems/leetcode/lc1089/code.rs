impl Solution {
    pub fn duplicate_zeros(arr: &mut Vec<i32>) {
        let n = arr.len();
        let src = arr.clone();

        let mut tmp: Vec<i32> = Vec::new();
        let mut read: usize = 0;

        while read < n {
            let v = src[read];
            if tmp.len() < n {
                tmp.push(v);
            }
            if v == 0 && tmp.len() < n {
                tmp.push(0);
            }
            read = read + 1;
        }

        let mut i: usize = 0;
        while i < n {
            let val = tmp[i];
            arr[i] = val;
            i = i + 1;
        }
    }
}
