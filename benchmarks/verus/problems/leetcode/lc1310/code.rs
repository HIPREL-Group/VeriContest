impl Solution {
    pub fn xor_queries(arr: Vec<i32>, queries: Vec<Vec<i32>>) -> Vec<i32> {
        let n = arr.len();
        let mut pref: Vec<i32> = Vec::new();
        pref.push(0);

        let mut i: usize = 0;
        while i < n {
            let next = pref[i] ^ arr[i];
            pref.push(next);
            i += 1;
        }

        let mut answer: Vec<i32> = Vec::new();
        let mut q: usize = 0;
        while q < queries.len() {
            let l_i32 = queries[q][0];
            let r_i32 = queries[q][1];
            let l = l_i32 as usize;
            let r = r_i32 as usize;
            let v = pref[r + 1] ^ pref[l];
            answer.push(v);
            q += 1;
        }

        answer
    }
}
