impl Solution {
    pub fn decode(encoded: Vec<i32>, first: i32) -> Vec<i32> {
        let mut ans = Vec::new();
        ans.push(first);
        let mut i = 0;
        while i < encoded.len() {
            let next = ans[i] ^ encoded[i];
            ans.push(next);
            i = i + 1;
        }
        ans
    }
}
