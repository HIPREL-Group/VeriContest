impl Solution {
    pub fn poor_pigs(buckets: i32, minutes_to_die: i32, minutes_to_test: i32) -> i32 {
        let states = minutes_to_test / minutes_to_die + 1;
        let mut pigs: i32 = 0;
        let mut capacity: i32 = 1;
        while capacity < buckets {
            let prod: i64 = capacity as i64 * states as i64;
            capacity = prod as i32;
            pigs += 1;
        }
        pigs
    }
}
