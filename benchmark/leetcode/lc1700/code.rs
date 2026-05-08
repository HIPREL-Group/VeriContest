impl Solution {
    pub fn count_students(students: Vec<i32>, sandwiches: Vec<i32>) -> i32 {
        let mut queue: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        while idx < students.len() {
            queue.push(students[idx]);
            idx = idx + 1;
        }
        let mut sand_idx: usize = 0;
        let mut skipped: usize = 0;
        while sand_idx < sandwiches.len() && skipped < queue.len() {
            if queue[0] == sandwiches[sand_idx] {
                let mut new_queue: Vec<i32> = Vec::new();
                let mut k: usize = 1;
                while k < queue.len() {
                    new_queue.push(queue[k]);
                    k = k + 1;
                }
                queue = new_queue;
                sand_idx = sand_idx + 1;
                skipped = 0;
            } else {
                let front: i32 = queue[0];
                let mut new_queue: Vec<i32> = Vec::new();
                let mut k: usize = 1;
                while k < queue.len() {
                    new_queue.push(queue[k]);
                    k = k + 1;
                }
                new_queue.push(front);
                queue = new_queue;
                skipped = skipped + 1;
            }
        }
        queue.len() as i32
    }
}
