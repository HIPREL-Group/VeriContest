use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn max2(a: int, b: int) -> int {
        if a >= b { a } else { b }
    }

    pub open spec fn max3(a: int, b: int, c: int) -> int {
        Self::max2(Self::max2(a, b), c)
    }

    pub open spec fn max4(a: int, b: int, c: int, d: int) -> int {
        Self::max2(Self::max3(a, b, c), d)
    }

    pub open spec fn encrypt_int(x: int) -> int {
        if x < 10 {
            x
        } else if x < 100 {
            let d0 = x % 10;
            let d1 = x / 10;
            11 * Self::max2(d0, d1)
        } else if x < 1000 {
            let d0 = x % 10;
            let d1 = (x / 10) % 10;
            let d2 = x / 100;
            111 * Self::max3(d0, d1, d2)
        } else {
            let d0 = x % 10;
            let d1 = (x / 10) % 10;
            let d2 = (x / 100) % 10;
            let d3 = x / 1000;
            1111 * Self::max4(d0, d1, d2, d3)
        }
    }

    pub open spec fn sum_encrypted(nums: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::sum_encrypted(nums, end - 1) + Self::encrypt_int(nums[end - 1] as int)
        }
    }

    proof fn lemma_encrypt_bounds(x: int)
        requires
            1 <= x <= 1000,
        ensures
            1 <= Self::encrypt_int(x) <= 9999,
    {
        if x < 10 {
        } else if x < 100 {
            assert(0 <= x % 10 <= 9);
            assert(0 <= x / 10 <= 9);
            assert(1 <= Self::max2(x % 10, x / 10) <= 9);
        } else if x < 1000 {
            assert(0 <= x % 10 <= 9);
            assert(0 <= (x / 10) % 10 <= 9);
            assert(0 <= x / 100 <= 9);
            assert(1 <= Self::max3(x % 10, (x / 10) % 10, x / 100) <= 9);
        } else {
            assert(x == 1000);
            assert(0 <= x % 10 <= 9);
            assert(0 <= (x / 10) % 10 <= 9);
            assert(0 <= (x / 100) % 10 <= 9);
            assert(0 <= x / 1000 <= 9);
            assert(1 <= Self::max4(x % 10, (x / 10) % 10, (x / 100) % 10, x / 1000) <= 9);
        }
    }

    proof fn lemma_sum_encrypted_bounds(nums: Seq<i32>, end: int)
        requires
            0 <= end <= nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
        ensures
            0 <= Self::sum_encrypted(nums, end) <= 9999 * end,
        decreases end,
    {
        if end > 0 {
            Self::lemma_sum_encrypted_bounds(nums, end - 1);
            Self::lemma_encrypt_bounds(nums[end - 1] as int);
        }
    }

    pub fn sum_of_encrypted_int(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 50,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
        ensures
            result as int == Self::sum_encrypted(nums@, nums.len() as int),
    {
        let mut sum: i32 = 0;
        for i in 0..nums.len()
            invariant
                1 <= nums.len() <= 50,
                forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 1000,
                sum as int == Self::sum_encrypted(nums@, i as int),
                0 <= sum as int <= 9999 * i as int,
        {
            let n = nums[i];
            let ghost x = nums@[i as int] as int;
            let enc: i32;
            if n < 10 {
                enc = n;
                proof {
                    assert(n as int == x);
                    assert(Self::encrypt_int(x) == x);
                    assert(enc as int == Self::encrypt_int(x));
                }
            } else if n < 100 {
                let d0 = n % 10;
                let d1 = n / 10;
                let m = if d0 >= d1 { d0 } else { d1 };
                proof {
                    assert(n as int == x);
                    assert(10 <= x < 100);
                    assert(d0 as int == x % 10);
                    assert(d1 as int == x / 10);
                    assert(m as int == Self::max2(x % 10, x / 10));
                    assert(1 <= m <= 9);
                }
                enc = 11 * m;
                proof {
                    assert(enc as int == 11 * Self::max2(x % 10, x / 10));
                    assert(Self::encrypt_int(x) == 11 * Self::max2(x % 10, x / 10));
                    assert(enc as int == Self::encrypt_int(x));
                }
            } else if n < 1000 {
                let d0 = n % 10;
                let d1 = (n / 10) % 10;
                let d2 = n / 100;
                let mut m = if d0 >= d1 { d0 } else { d1 };
                if d2 > m {
                    m = d2;
                }
                proof {
                    assert(n as int == x);
                    assert(100 <= x < 1000);
                    assert(d0 as int == x % 10);
                    assert(d1 as int == (x / 10) % 10);
                    assert(d2 as int == x / 100);
                    assert(m as int == Self::max3(x % 10, (x / 10) % 10, x / 100));
                    assert(1 <= m <= 9);
                }
                enc = 111 * m;
                proof {
                    assert(enc as int == 111 * Self::max3(x % 10, (x / 10) % 10, x / 100));
                    assert(Self::encrypt_int(x) == 111 * Self::max3(x % 10, (x / 10) % 10, x / 100));
                    assert(enc as int == Self::encrypt_int(x));
                }
            } else {
                let d0 = n % 10;
                let d1 = (n / 10) % 10;
                let d2 = (n / 100) % 10;
                let d3 = n / 1000;
                let mut m = if d0 >= d1 { d0 } else { d1 };
                if d2 > m {
                    m = d2;
                }
                if d3 > m {
                    m = d3;
                }
                proof {
                    assert(n as int == x);
                    assert(x == 1000);
                    assert(d0 as int == x % 10);
                    assert(d1 as int == (x / 10) % 10);
                    assert(d2 as int == (x / 100) % 10);
                    assert(d3 as int == x / 1000);
                    assert(m as int == Self::max4(x % 10, (x / 10) % 10, (x / 100) % 10, x / 1000));
                    assert(1 <= m <= 9);
                }
                enc = 1111 * m;
                proof {
                    assert(enc as int == 1111 * Self::max4(x % 10, (x / 10) % 10, (x / 100) % 10, x / 1000));
                    assert(Self::encrypt_int(x) == 1111 * Self::max4(x % 10, (x / 10) % 10, (x / 100) % 10, x / 1000));
                    assert(enc as int == Self::encrypt_int(x));
                }
            }
            proof {
                Self::lemma_sum_encrypted_bounds(nums@, i as int);
                Self::lemma_sum_encrypted_bounds(nums@, i as int + 1);
            }
            sum = sum + enc;
            proof {
                assert(Self::sum_encrypted(nums@, i as int + 1)
                    == Self::sum_encrypted(nums@, i as int) + Self::encrypt_int(nums@[i as int] as int));
                assert(sum as int == Self::sum_encrypted(nums@, i as int + 1));
            }
        }
        sum
    }
}

}
