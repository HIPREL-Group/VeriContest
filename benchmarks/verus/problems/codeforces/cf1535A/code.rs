impl Solution {
    pub fn fair_playoff(s1: i64, s2: i64, s3: i64, s4: i64) -> bool {
        let w1 = if s1 >= s2 { s1 } else { s2 };
        let w2 = if s3 >= s4 { s3 } else { s4 };
        let l1 = if s1 <= s2 { s1 } else { s2 };
        let l2 = if s3 <= s4 { s3 } else { s4 };
        let weaker_winner = if w1 <= w2 { w1 } else { w2 };
        let stronger_loser = if l1 >= l2 { l1 } else { l2 };
        weaker_winner > stronger_loser
    }
}
