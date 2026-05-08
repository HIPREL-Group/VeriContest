impl Solution {
    pub fn add_rungs(rungs: Vec<i32>, dist: i32) -> i32 {
        let mut result: i32 = 0;
        let mut prev: i32 = 0;
        let n = rungs.len();
        let mut i: usize = 0;

        while i < n {
            let gap = rungs[i] - prev;
            let added = (gap - 1) / dist;
            result = result + added;
            prev = rungs[i];
            i += 1;
        }

        result
    }
}
