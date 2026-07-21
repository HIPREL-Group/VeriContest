impl Solution {
    pub fn number_of_alternating_groups(colors: Vec<i32>) -> i32 {
        let n = colors.len();
        let mut count = 0i32;
        let mut i = 0;
        while i < n {
            let prev = (i + n - 1) % n;
            let next = (i + 1) % n;
            if colors[i] != colors[prev] && colors[i] != colors[next] {
                count = count + 1;
            }
            i = i + 1;
        }
        count
    }
}
