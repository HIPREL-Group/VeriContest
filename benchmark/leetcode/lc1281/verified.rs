use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn digit_product_bounded(n: nat, digits: nat) -> int
    decreases digits,
{
    if digits == 0 {
        1int
    } else {
        (n % 10) as int * digit_product_bounded(n / 10, (digits - 1) as nat)
    }
}

pub open spec fn digit_sum_bounded(n: nat, digits: nat) -> int
    decreases digits,
{
    if digits == 0 {
        0int
    } else {
        (n % 10) as int + digit_sum_bounded(n / 10, (digits - 1) as nat)
    }
}

pub open spec fn digit_product(n: nat) -> int {
    digit_product_bounded(n, 6)
}

pub open spec fn digit_sum(n: nat) -> int {
    digit_sum_bounded(n, 6)
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

proof fn lemma_pow9_positive(k: nat)
    ensures
        pow9(k) >= 1,
    decreases k,
{
    if k == 0 {
    } else {
        lemma_pow9_positive((k - 1) as nat);
    }
}

proof fn lemma_product_bound_step(product: int, digit: int, bound: int)
    requires
        0 <= product <= bound,
        0 <= digit <= 9,
    ensures
        0 <= product * digit <= 9 * bound,
{
    assert(product * digit <= 9 * bound) by(nonlinear_arith)
        requires
            0 <= product <= bound,
            0 <= digit <= 9,
    {}
    assert(product * digit >= 0) by(nonlinear_arith)
        requires
            product >= 0,
            digit >= 0,
    {}
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
        let mut cnt: u32 = 0;

        while cnt < 6
            invariant
                0 <= num <= 100000,
                cnt <= 6,
                0 <= product <= pow9(cnt as nat),
                product * digit_product_bounded(num as nat, (6 - cnt) as nat)
                    == digit_product(n as nat),
                sum + digit_sum_bounded(num as nat, (6 - cnt) as nat)
                    == digit_sum(n as nat),
                0 <= sum <= 9 * cnt,
                pow9(cnt as nat) <= 531441,
            decreases 6 - cnt,
        {
            let digit = num % 10;
            assert(0 <= digit <= 9);

            proof {
                assert(digit as nat == (num as nat) % 10);
                let d = (6 - cnt) as nat;
                assert(d > 0);

                
                assert(digit_product_bounded(num as nat, d)
                    == (num as nat % 10) as int
                        * digit_product_bounded((num as nat) / 10, (d - 1) as nat));
                assert(digit_sum_bounded(num as nat, d)
                    == (num as nat % 10) as int
                        + digit_sum_bounded((num as nat) / 10, (d - 1) as nat));

                
                assert(product * digit as i64
                    * digit_product_bounded((num / 10) as nat, (d - 1) as nat)
                    == digit_product(n as nat)) by(nonlinear_arith)
                    requires
                        product * digit_product_bounded(num as nat, d)
                            == digit_product(n as nat),
                        digit_product_bounded(num as nat, d)
                            == digit as int
                                * digit_product_bounded((num / 10) as nat, (d - 1) as nat),
                {}

                
                lemma_product_bound_step(product as int, digit as int, pow9(cnt as nat));
                assert(9 * pow9(cnt as nat) == pow9((cnt + 1) as nat));

                lemma_pow9_positive((cnt + 1) as nat);
                assert(pow9((cnt + 1) as nat) <= 531441) by {
                    assert(pow9(0nat) == 1);
                    assert(pow9(1nat) == 9 * pow9(0nat));
                    assert(pow9(2nat) == 9 * pow9(1nat));
                    assert(pow9(3nat) == 9 * pow9(2nat));
                    assert(pow9(4nat) == 9 * pow9(3nat));
                    assert(pow9(5nat) == 9 * pow9(4nat));
                    assert(pow9(6nat) == 9 * pow9(5nat));
                }
            }

            product = product * digit as i64;
            sum = sum + digit as i64;
            num = num / 10;
            cnt = cnt + 1;
        }

        assert(digit_product_bounded(num as nat, 0nat) == 1int);
        assert(digit_sum_bounded(num as nat, 0nat) == 0int);
        assert(product == digit_product(n as nat));
        assert(sum == digit_sum(n as nat));

        (product - sum) as i32
    }
}

} 
