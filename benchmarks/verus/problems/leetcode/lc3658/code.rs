impl Solution {
    pub fn gcd_of_odd_even_sums(n: i32) -> i32 
    {

        let mut a: i32 = n * n;
        let mut b: i32 = n * (n - 1);
        while b != 0 
        {
            let rem = a % b;
            a = b;
            b = rem;
        }
        a
    }

}

