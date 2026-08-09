impl Solution {
    pub fn minimum_card_pickup(cards: Vec<i32>) -> i32 {
        let n = cards.len();
        let mut last_seen: Vec<i32> = Vec::new();
        let mut vi: usize = 0;
        while vi <= 1_000_000 {
            last_seen.push(-1);
            vi += 1;
        }

        let mut min_pickup: i32 = -1;
        let mut i: usize = 0;
        while i < n {
            let v = cards[i] as usize;
            let prev = last_seen[v];
            if prev != -1 {
                let cand = (i as i32) - prev + 1;
                if min_pickup == -1 || cand < min_pickup {
                    min_pickup = cand;
                }
            }
            last_seen[v] = i as i32;
            i += 1;
        }

        min_pickup
    }
}
