use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn digit_product(n: nat) -> int
    decreases n,
{
    if n == 0 {
        1int
    } else {
        (n % 10) as int * digit_product((n / 10) as nat)
    }
}

pub open spec fn digit_sum(n: nat) -> int
    decreases n,
{
    if n == 0 {
        0int
    } else {
        (n % 10) as int + digit_sum((n / 10) as nat)
    }
}

pub open spec fn pow9(k: nat) -> int
    decreases k,
{
    if k == 0 {
        1int
    } else {
        9 * pow9((k - 1) as nat)
    }
}

pub open spec fn pow10(k: nat) -> int
    decreases k,
{
    if k == 0 {
        1int
    } else {
        10 * pow10((k - 1) as nat)
    }
}

proof fn pow9_pos(k: nat)
    ensures
        pow9(k) >= 1,
    decreases k,
{
    if k > 0 {
        pow9_pos((k - 1) as nat);
    }
}

proof fn pow9_le(a: nat, b: nat)
    requires
        a <= b,
    ensures
        pow9(a) <= pow9(b),
    decreases b,
{
    if a < b {
        pow9_le(a, (b - 1) as nat);
        pow9_pos((b - 1) as nat);
    }
}

impl Solution {
    pub fn subtract_product_and_sum(n: i32) -> (res: i32)
        requires
            1 <= n <= 100000,
        ensures
            res == digit_product(n as nat) - digit_sum(n as nat),
    {
        let mut num: i32 = n;
        let mut product: i64 = 1;
        let mut sum: i64 = 0;
        let ghost mut cnt: nat = 0;

        assert(pow10(6nat) == 1000000) by (compute);

        while num > 0
            invariant
                0 <= num <= 100000,
                cnt <= 6,
                num < pow10((6 - cnt) as nat),
                0 <= product,
                product <= pow9(cnt),
                0 <= sum <= 9 * cnt,
                (product as int) * digit_product(num as nat) == digit_product(n as nat),
                (sum as int) + digit_sum(num as nat) == digit_sum(n as nat),
            decreases num,
        {
            let ghost cnt0 = cnt;
            let ghost num0 = num;
            let ghost p0 = product;
            let ghost s0 = sum;
            let digit = num % 10;
            assert(0 <= digit < 10);

            proof {
                if cnt0 >= 6 {
                    assert((6 - cnt0) as nat == 0nat);
                    assert(pow10(0nat) == 1);
                    assert(false);
                }
                assert(cnt0 <= 5);
                assert(p0 <= pow9(cnt0));
                pow9_pos(cnt0);
                pow9_le(cnt0, 6nat);
                assert(pow9(6nat) == 531441) by (compute);
                assert(p0 <= 531441);
                assert((p0 as int) * (digit as int) <= 4782969) by (nonlinear_arith)
                    requires
                        0 <= p0 <= 531441,
                        0 <= digit < 10,
                ;
                assert((p0 as int) * (digit as int) >= 0) by (nonlinear_arith)
                    requires
                        0 <= p0,
                        0 <= digit,
                ;
                assert(digit as nat == (num0 as nat) % 10);
                assert((num0 / 10) as nat == (num0 as nat) / 10);
                assert(digit_product(num0 as nat)
                    == (digit as int) * digit_product((num0 / 10) as nat));
                assert(digit_sum(num0 as nat)
                    == (digit as int) + digit_sum((num0 / 10) as nat));
            }

            product = product * digit as i64;
            sum = sum + digit as i64;
            num = num / 10;

            proof {
                cnt = cnt + 1;
                assert(product as int == (p0 as int) * (digit as int));
                assert(sum as int == (s0 as int) + (digit as int));
                assert(num as nat == (num0 / 10) as nat);
                assert(pow9(cnt) == 9 * pow9(cnt0));
                assert((p0 as int) * (digit as int) <= 9 * pow9(cnt0)) by (nonlinear_arith)
                    requires
                        0 <= p0,
                        p0 <= pow9(cnt0),
                        0 <= digit < 10,
                        pow9(cnt0) >= 0,
                ;
                assert(digit_product(num as nat) == digit_product((num0 / 10) as nat));
                assert((product as int) * digit_product(num as nat)
                    == (p0 as int) * ((digit as int) * digit_product((num0 / 10) as nat)))
                    by (nonlinear_arith)
                    requires
                        product as int == (p0 as int) * (digit as int),
                        digit_product(num as nat) == digit_product((num0 / 10) as nat),
                ;
                assert((digit as int) * digit_product((num0 / 10) as nat)
                    == digit_product(num0 as nat));
                assert(digit_sum(num as nat) == digit_sum((num0 / 10) as nat));
                assert((6 - cnt0) as nat == ((6 - cnt) as nat) + 1);
                assert(pow10((6 - cnt0) as nat) == 10 * pow10((6 - cnt) as nat));
            }
        }

        proof {
            assert(num == 0);
            assert(digit_product(0nat) == 1);
            assert(digit_sum(0nat) == 0);
            pow9_le(cnt, 6nat);
            assert(pow9(6nat) == 531441) by (compute);
            assert(product <= 531441);
        }

        (product - sum) as i32
    }
}

}