impl Solution {
    pub fn minimum_card_pickup(cards: Vec<i32>) -> i32 {
        let mut min_pickup = i32::MAX;
        let n = cards.len();
        
        let mut i: usize = 0;
        while i < n {
            let mut j: usize = i + 1;
            while j < n {
                if cards[i] == cards[j] {
                    let pickup = (j - i + 1) as i32;
                    if pickup < min_pickup {
                        min_pickup = pickup;
                    }
                    j = n;
                } else {
                    j = j + 1;
                }
            }
            i = i + 1;
        }
        
        if min_pickup == i32::MAX {
            -1
        } else {
            min_pickup
        }
    }
}
