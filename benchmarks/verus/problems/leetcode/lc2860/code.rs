impl Solution {
    pub fn count_ways(nums: Vec<i32>) -> i32 {
        let n = nums.len();

        let mut cnt: Vec<i64> = Vec::new();
        let mut vi: usize = 0;
        while vi <= n {
            cnt.push(0);
            vi += 1;
        }

        let mut i: usize = 0;
        while i < n {
            let val = nums[i] as usize;
            cnt[val] = cnt[val] + 1;
            i += 1;
        }

        let mut prefix: Vec<i64> = Vec::new();
        prefix.push(0);
        let mut v1: usize = 1;
        while v1 <= n {
            let next = prefix[v1 - 1] + cnt[v1 - 1];
            prefix.push(next);
            v1 += 1;
        }

        let mut ways: i64 = 0;
        let mut x: usize = 0;
        while x <= n {
            if prefix[x] == x as i64 && cnt[x] == 0 {
                ways += 1;
            }
            x += 1;
        }

        ways as i32
    }
}
