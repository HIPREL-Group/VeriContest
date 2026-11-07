impl Solution {
    fn set_flag(flags: &mut Vec<bool>, idx: usize, value: bool)
    {
        flags[idx] = value;
    }

    pub fn fair_candy_swap(alice_sizes: Vec<i32>, bob_sizes: Vec<i32>) -> Vec<i32>
    {
        let mut sum_a = 0i128;
        let mut i = 0usize;
        while i < alice_sizes.len()
        {
            sum_a = sum_a + alice_sizes[i] as i128;
            i = i + 1;
        }

        let mut sum_b = 0i128;
        i = 0usize;
        while i < bob_sizes.len()
        {
            sum_b = sum_b + bob_sizes[i] as i128;
            i = i + 1;
        }

        let delta = (sum_a - sum_b) / 2;

        let mut present: Vec<bool> = Vec::new();
        let mut size = 0usize;
        while size <= 100000usize
        {
            present.push(false);
            size = size + 1;
        }

        i = 0usize;
        while i < alice_sizes.len()
        {
            let idx = alice_sizes[i] as usize;
            Self::set_flag(&mut present, idx, true);
            i = i + 1;
        }

        let mut j = 0usize;
        while j < bob_sizes.len()
        {
            let target = bob_sizes[j] as i128 + delta as i128;
            if 1 <= target && target <= 100000 && present[target as usize] {
                let mut answer = Vec::new();
                answer.push(target as i32);
                answer.push(bob_sizes[j]);
                return answer;
            }
            j = j + 1;
        }

        Vec::new()
    }
}
