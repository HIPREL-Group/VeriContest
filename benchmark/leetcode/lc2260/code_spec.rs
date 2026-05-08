use vstd::prelude::*;

fn main() {}

verus! {
    pub struct Solution;

    impl Solution {
        pub fn minimum_card_pickup(cards: Vec<i32>) -> (res: i32)
            requires
                1 <= cards.len() <= 100000,
                forall|i: int| 0 <= i < cards.len() ==> 0 <= #[trigger] cards[i] <= 1000000,
            ensures
                res == -1 ==> (forall|i: int, j: int| 0 <= i < j < cards.len() as int ==> #[trigger] cards[i] != #[trigger] cards[j]),
                res != -1 ==> (exists|i: int, j: int| 0 <= i < j < cards.len() as int && #[trigger] cards[i] == #[trigger] cards[j] && res as int == j - i + 1),
                res != -1 ==> (forall|i: int, j: int| 0 <= i < j < cards.len() as int && #[trigger] cards[i] == #[trigger] cards[j] ==> res as int <= j - i + 1),
        {
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
}
