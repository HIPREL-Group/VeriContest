impl Solution {
    pub fn football_kit_games(home: Vec<i32>, away: Vec<i32>) -> (Vec<i32>, Vec<i32>) {
        let n = home.len();
        let mut freq = Vec::new();
        let mut z = 0usize;
        while z < 100001 {
            freq.push(0i32);
            z += 1;
        }
        let mut i = 0usize;
        while i < n {
            let cidx = home[i] as usize;
            let oldv = freq[cidx];
            let newv = oldv + 1;
            freq[cidx] = newv;
            i += 1;
        }
        let mut games_home_kit = Vec::new();
        let mut games_away_kit = Vec::new();
        let mut j = 0usize;
        let nn = n as i32;
        while j < n {
            let aj = away[j];
            let c = aj as usize;
            let cnt = freq[c];
            games_home_kit.push((nn - 1) + cnt);
            games_away_kit.push((nn - 1) - cnt);
            j += 1;
        }
        (games_home_kit, games_away_kit)
    }
}
