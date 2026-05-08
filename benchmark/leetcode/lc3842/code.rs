impl Solution {
    pub fn toggle_light_bulbs(bulbs: Vec<i32>) -> Vec<i32> {
        let mut state: Vec<bool> = vec![false; 101];
        let mut i: usize = 0;
        while i < bulbs.len() {
            let b: usize = bulbs[i] as usize;
            state[b] = !state[b];
            i = i + 1;
        }

        let mut res: Vec<i32> = Vec::new();
        let mut b: usize = 1;
        while b <= 100 {
            let cur_b: usize = b;
            if state[cur_b] {
                res.push(cur_b as i32);
            }
            b = b + 1;
        }
        res
    }
}
