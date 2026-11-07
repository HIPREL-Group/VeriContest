impl Solution {
    pub fn num_pairs_divisible_by60(time: Vec<i32>) -> i32 {
        let mut counts: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < 60 {
            counts.push(0i32);
            j += 1;
        }

        let mut result: i32 = 0;
        let mut i: usize = 0;
        while i < time.len() {
            let ti = time[i];
            let r = (ti % 60) as usize;
            let comp = ((60 - ti % 60) % 60) as usize;
            result = result + counts[comp];
            counts[r] = counts[r] + 1;
            i += 1;
        }
        result
    }
}
