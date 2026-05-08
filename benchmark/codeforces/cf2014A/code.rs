impl Solution {
    pub fn count_people_helped(people: Vec<i64>, k: i64) -> usize {
        let mut gold: i64 = 0;
        let mut helped: usize = 0;
        let mut i: usize = 0;
        while i < people.len() {
            let ai = people[i];
            if ai >= k {
                gold = gold + ai;
            } else if ai == 0 && gold > 0 {
                gold = gold - 1;
                helped = helped + 1;
            }
            i = i + 1;
        }
        helped
    }
}
