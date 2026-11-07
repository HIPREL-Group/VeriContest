impl Solution {
    pub fn can_transform(a: Vec<i32>, b: Vec<i32>) -> bool {
        let n = a.len();
        let mut carry: i64 = 0;
        let mut val: i32 = -100;

        while val <= 100 {
            let mut av: usize = 0;
            let mut vi: usize = 0;
            while vi < n {
                if a[vi] == val {
                    av = av + 1;
                }
                vi = vi + 1;
            }

            let mut bv: usize = 0;
            vi = 0;
            while vi < n {
                if b[vi] == val {
                    bv = bv + 1;
                }
                vi = vi + 1;
            }

            let next = av as i64 - bv as i64 + carry;
            if next < 0 || next > av as i64 {
                return false;
            }

            carry = next;
            val = val + 1;
        }

        carry == 0
    }
}
