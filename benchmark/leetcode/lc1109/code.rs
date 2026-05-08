impl Solution {
    pub fn corp_flight_bookings(bookings: Vec<Vec<i32>>, n: i32) -> Vec<i32> {
        let nn = n as usize;
        let mut diff: Vec<i64> = Vec::new();
        let mut fill = 0usize;

        while fill <= nn {
            diff.push(0);
            fill += 1;
        }

        let mut i = 0usize;
        while i < bookings.len() {
            let first = bookings[i][0] as usize;
            let last = bookings[i][1] as usize;
            let seats = bookings[i][2] as i64;
            let add_value = diff[first - 1] + seats;
            let sub_value = diff[last] - seats;
            diff[first - 1] = add_value;
            diff[last] = sub_value;
            i += 1;
        }

        let mut result: Vec<i32> = Vec::new();
        let mut current = 0i64;
        let mut f = 0usize;
        while f < nn {
            let next = current + diff[f];
            current = next;
            result.push(current as i32);
            f += 1;
        }

        result
    }
}
