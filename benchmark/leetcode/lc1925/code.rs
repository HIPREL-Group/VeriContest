impl Solution {
    pub fn count_triples(n: i32) -> i32
    {
        let max_sq: i32 = n * n;
        let mut is_sq: Vec<bool> = Vec::new();
        let mut idx: i32 = 0;
        while idx <= max_sq
        {
            is_sq.push(false);
            idx = idx + 1;
        }
        let mut c: i32 = 1;
        while c <= n
        {
            is_sq[(c * c) as usize] = true;
            c = c + 1;
        }
        let mut count: i32 = 0;
        let mut a: i32 = 1;
        while a <= n
        {
            let mut b: i32 = 1;
            while b <= n
            {
                let s: i32 = a * a + b * b;
                if s <= max_sq && is_sq[s as usize] {
                    count = count + 1;
                }
                b = b + 1;
            }
            a = a + 1;
        }
        count
    }
}
