use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn get_bit(x: i32, i: u32) -> bool
        recommends
            0 <= i < 32,
    {
        (x >> i) & 1 == 1
    }

    pub fn reverse_bits(n: i32) -> (res: i32)
        requires
            0 <= n <= 2_147_483_646,
            n % 2 == 0,
        ensures
            forall|i: int|
                0 <= i < 32 ==> #[trigger] Solution::get_bit(res, i as u32) == Solution::get_bit(
                    n,
                    (31 - i) as u32,
                ),
    {
        let (mut res, mut x) = (0i32, n);

        assert(n >> 0 == n) by (bit_vector);

        let mut i: u32 = 0;
        while i < 32
            invariant
                0 <= i <= 32,
                x == n >> i,
                forall|j: int|
                    0 <= j < i ==> #[trigger] Solution::get_bit(res, j as u32) == Solution::get_bit(
                        n,
                        (i - 1 - j) as u32,
                    ),
            decreases 32 - i,
        {
            let ghost old_i = i;

            proof {
                assert((((res << 1) | (x & 1)) >> 0) & 1 == 1 <==> (n >> i) & 1 == 1)
                    by (bit_vector)
                    requires
                        i < 32,
                        x == n >> i,
                ;

                assert forall|j_u32: u32| #![auto] j_u32 < i implies ((((res << 1) | (x & 1)) >> (
                j_u32 + 1)) & 1) == ((res >> j_u32) & 1) by {
                    assert((((res << 1) | (x & 1)) >> (j_u32 + 1)) & 1 == (res >> j_u32) & 1)
                        by (bit_vector)
                        requires
                            j_u32 < i,
                            i < 32,
                    ;
                }
            }

            let new_res = (res << 1) | (x & 1);
            let new_x = x >> 1;

            proof {
                assert forall|j: int| 0 <= j < old_i implies #[trigger] Solution::get_bit(
                    new_res,
                    (j + 1) as u32,
                ) == Solution::get_bit(n, (old_i - 1 - j) as u32) by {
                    let j_u32 = j as u32;
                    assert(Solution::get_bit(res, j_u32) == Solution::get_bit(
                        n,
                        (old_i - 1 - j_u32) as u32,
                    ));
                    assert(((new_res >> (j_u32 + 1)) & 1) == ((res >> j_u32) & 1));
                    assert(Solution::get_bit(new_res, (j + 1) as u32) == Solution::get_bit(
                        n,
                        (old_i - 1 - j) as u32,
                    ));
                }

                assert(new_x == n >> (old_i + 1)) by (bit_vector)
                    requires
                        new_x == x >> 1,
                        old_i < 32,
                        x == n >> old_i,
                ;
            }

            res = new_res;
            x = new_x;
            i += 1;

            proof {
                assert forall|j: int| 0 <= j < i implies #[trigger] Solution::get_bit(res, j as u32)
                    == Solution::get_bit(n, (i - 1 - j) as u32) by {
                    if j == 0 {
                        assert(Solution::get_bit(res, 0) == Solution::get_bit(n, old_i));
                    } else {
                        let j_old = (j - 1) as int;
                        assert(Solution::get_bit(new_res, (j_old + 1) as u32) == Solution::get_bit(
                            n,
                            (old_i - 1 - j_old) as u32,
                        ));
                    }
                }
            }
        }

        assert forall|j: int| 0 <= j < 32 implies #[trigger] Solution::get_bit(res, j as u32)
            == Solution::get_bit(n, (31 - j) as u32) by {
            assert(i == 32);
            assert(0 <= j < i);
            assert(i - 1 - j == 31 - j);
            assert(Solution::get_bit(res, j as u32) == Solution::get_bit(n, (i - 1 - j) as u32));
        }

        res
    }
}

} 
