impl Solution {
    pub fn merge_triplets(triplets: Vec<Vec<i32>>, target: Vec<i32>) -> bool {
        let mut has0 = false;
        let mut has1 = false;
        let mut has2 = false;
        let mut i = 0usize;

        while i < triplets.len() {
            let t0 = triplets[i][0];
            let t1 = triplets[i][1];
            let t2 = triplets[i][2];

            has0 = has0 || (t0 == target[0] && t1 <= target[1] && t2 <= target[2]);
            has1 = has1 || (t0 <= target[0] && t1 == target[1] && t2 <= target[2]);
            has2 = has2 || (t0 <= target[0] && t1 <= target[1] && t2 == target[2]);

            i += 1;
        }

        has0 && has1 && has2
    }
}