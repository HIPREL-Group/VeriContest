impl Solution {
    pub fn count_magnet_groups(magnets: Vec<u8>) -> u32 {
        let n = magnets.len();
        let mut groups = 1u32;
        let mut i = 1usize;
        while i < n {
            if magnets[i] != magnets[i - 1] {
                groups += 1;
            }
            i += 1;
        }
        groups
    }
}
