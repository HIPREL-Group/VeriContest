impl Solution {
    pub fn car_pooling(trips: Vec<Vec<i32>>, capacity: i32) -> bool {
        let mut diff: Vec<i64> = Vec::new();
        let mut fill = 0usize;

        while fill < 1001 {
            diff.push(0);
            fill += 1;
        }

        let mut i = 0usize;
        while i < trips.len() {
            let passengers = trips[i][0] as i64;
            let from = trips[i][1] as usize;
            let to = trips[i][2] as usize;
            let add_value = diff[from] + passengers;
            let sub_value = diff[to] - passengers;

            diff[from] = add_value;
            diff[to] = sub_value;
            i += 1;
        }

        let mut current = 0i64;
        let mut stop = 0usize;
        while stop < 1001 {
            let next = current + diff[stop];
            current = next;
            if current > capacity as i64 {
                return false;
            }
            stop += 1;
        }

        true
    }
}
