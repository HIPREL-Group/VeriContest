impl Solution {
    pub fn split_num(num: i32) -> i32 {
        let mut cnt: Vec<i32> = vec![0; 10];
        let mut x = num;
        while x > 0 {
            let d = (x % 10) as usize;
            cnt[d] = cnt[d] + 1;
            x = x / 10;
        }

        let mut a: i32 = 0;
        let mut b: i32 = 0;
        let mut turn_a = true;
        let mut d: usize = 0;
        while d <= 9 {
            while cnt[d] > 0 {
                if turn_a {
                    a = a * 10 + d as i32;
                } else {
                    b = b * 10 + d as i32;
                }
                turn_a = !turn_a;
                cnt[d] = cnt[d] - 1;
            }
            d = d + 1;
        }
        a + b
    }
}
