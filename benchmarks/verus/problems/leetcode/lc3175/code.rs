impl Solution {
    pub fn find_winning_player(skills: Vec<i32>, k: i32) -> i32 {
        let n = skills.len();
        let mut champ = 0usize;
        let mut win = 0i64;
        let mut j = 1usize;
        while j < n && win < k as i64 {
            if skills[j] > skills[champ] {
                champ = j;
                win = 0;
            }
            win = win.checked_add(1).unwrap_or(win);
            j += 1;
        }
        champ as i32
    }
}
