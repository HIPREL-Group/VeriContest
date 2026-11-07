impl Solution {
    pub fn count_beautiful_subsequences(a: Vec<i32>) -> u64 {
        let n = a.len();
        let mut result: u64 = 0;

        let mut i: usize = 0;
        while i < n {
            if a[i] == 3 && i >= 2 {
                let mut j: usize = 0;
                while j < i {
                    if a[j] == 1 {
                        let mut count_2s: u32 = 0;
                        let mut k: usize = j + 1;
                        while k < i {
                            if a[k] == 2 {
                                count_2s += 1;
                            }
                            k += 1;
                        }

                        let mut ways: u64 = 1;
                        let mut exp: u32 = 0;
                        while exp < count_2s {
                            ways = (ways * 2) % 998244353u64;
                            exp += 1;
                        }

                        let contrib = (((ways as u128) + 998244353u128 - 1)
                            % 998244353u128) as u64;
                        result = (result + contrib) % 998244353u64;
                    }
                    j += 1;
                }
            }
            i += 1;
        }

        result
    }
}
