impl Solution {
    pub fn recover_order(order: Vec<i32>, friends: Vec<i32>) -> Vec<i32> {
        let mut result: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < order.len() {
            let candidate = order[i];
            let mut j: usize = 0;
            let mut found = false;
            while j < friends.len() {
                if friends[j] == candidate {
                    found = true;
                }
                j = j + 1;
            }
            if found {
                result.push(candidate);
            }
            i = i + 1;
        }
        result
    }
}
