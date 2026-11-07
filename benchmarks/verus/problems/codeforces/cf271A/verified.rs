use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn digit_at(y: int, pos: int) -> int
    recommends
        1000 <= y <= 9999,
        0 <= pos < 4,
{
    (y / (if pos == 0 { 1 } else if pos == 1 { 10 } else if pos == 2 { 100 } else { 1000 })) % 10
}

pub open spec fn distinct_digits(y: int) -> bool
    recommends 1000 <= y <= 9999,
{
    forall|i: int|
        0 <= i < 4 ==> forall|j: int|
            0 <= j < 4 && i != j ==> #[trigger] digit_at(y, i) != digit_at(y, j)
}

proof fn lemma_digit_at_0(y: int)
    requires 1000 <= y <= 9999,
    ensures digit_at(y, 0) == y % 10,
{
}

proof fn lemma_digit_at_1(y: int)
    requires 1000 <= y <= 9999,
    ensures digit_at(y, 1) == (y / 10) % 10,
{
}

proof fn lemma_digit_at_2(y: int)
    requires 1000 <= y <= 9999,
    ensures digit_at(y, 2) == (y / 100) % 10,
{
}

proof fn lemma_digit_at_3(y: int)
    requires 1000 <= y <= 9999,
    ensures digit_at(y, 3) == (y / 1000) % 10,
{
}

proof fn lemma_1023_beautiful()
    ensures distinct_digits(1023),
{
    lemma_digit_at_0(1023);
    lemma_digit_at_1(1023);
    lemma_digit_at_2(1023);
    lemma_digit_at_3(1023);
    assert(digit_at(1023, 0) == 3);
    assert(digit_at(1023, 1) == 2);
    assert(digit_at(1023, 2) == 0);
    assert(digit_at(1023, 3) == 1);
    assert(forall|i: int, j: int|
        0 <= i < 4 && 0 <= j < 4 && i != j ==> digit_at(1023, i) != digit_at(1023, j));
}

proof fn lemma_9012_beautiful()
    ensures distinct_digits(9012),
{
    lemma_digit_at_0(9012);
    lemma_digit_at_1(9012);
    lemma_digit_at_2(9012);
    lemma_digit_at_3(9012);
    assert(digit_at(9012, 0) == 2);
    assert(digit_at(9012, 1) == 1);
    assert(digit_at(9012, 2) == 0);
    assert(digit_at(9012, 3) == 9);
    assert(forall|i: int, j: int|
        0 <= i < 4 && 0 <= j < 4 && i != j ==> digit_at(9012, i) != digit_at(9012, j));
}

proof fn lemma_not_distinct_digits(y: int, d0: int, d1: int, d2: int, d3: int)
    requires
        1000 <= y <= 9999,
        d0 == y % 10,
        d1 == (y / 10) % 10,
        d2 == (y / 100) % 10,
        d3 == (y / 1000) % 10,
        !(d0 != d1 && d0 != d2 && d0 != d3 && d1 != d2 && d1 != d3 && d2 != d3),
    ensures
        !distinct_digits(y),
{
    lemma_digit_at_0(y);
    lemma_digit_at_1(y);
    lemma_digit_at_2(y);
    lemma_digit_at_3(y);
    assert(digit_at(y, 0) == d0);
    assert(digit_at(y, 1) == d1);
    assert(digit_at(y, 2) == d2);
    assert(digit_at(y, 3) == d3);
    if d0 == d1 {
        assert(digit_at(y, 0) == digit_at(y, 1));
    } else if d0 == d2 {
        assert(digit_at(y, 0) == digit_at(y, 2));
    } else if d0 == d3 {
        assert(digit_at(y, 0) == digit_at(y, 3));
    } else if d1 == d2 {
        assert(digit_at(y, 1) == digit_at(y, 2));
    } else if d1 == d3 {
        assert(digit_at(y, 1) == digit_at(y, 3));
    } else {
        assert(d2 == d3);
        assert(digit_at(y, 2) == digit_at(y, 3));
    }
    assert(exists|i: int, j: int|
        0 <= i < 4 && 0 <= j < 4 && i != j && digit_at(y, i) == digit_at(y, j));
}

proof fn lemma_distinct_digits_equiv(y: int, d0: int, d1: int, d2: int, d3: int)
    requires
        1000 <= y <= 9999,
        d0 == y % 10,
        d1 == (y / 10) % 10,
        d2 == (y / 100) % 10,
        d3 == (y / 1000) % 10,
        d0 != d1,
        d0 != d2,
        d0 != d3,
        d1 != d2,
        d1 != d3,
        d2 != d3,
    ensures
        distinct_digits(y),
{
    lemma_digit_at_0(y);
    lemma_digit_at_1(y);
    lemma_digit_at_2(y);
    lemma_digit_at_3(y);
    assert(digit_at(y, 0) == d0);
    assert(digit_at(y, 1) == d1);
    assert(digit_at(y, 2) == d2);
    assert(digit_at(y, 3) == d3);
    assert(forall|i: int, j: int|
        0 <= i < 4 && 0 <= j < 4 && i != j ==> digit_at(y, i) != digit_at(y, j));
}

impl Solution {
    pub fn beautiful_year(n: i32) -> (res: i32)
        requires
            1000 <= n <= 9000,
        ensures
            res as int > n as int,
            1000 <= res as int <= 9999,
            distinct_digits(res as int),
            forall|k: int|
                (n as int) < k && k < (res as int) ==> !distinct_digits(k),
    {
        let mut y = n + 1;
        while y <= 9999
            invariant
                1000 <= n <= 9000,
                n + 1 <= y <= 10000,
                forall|k: int|
                    (n as int) < k && k < (y as int) ==> !distinct_digits(k),
            decreases 10000 - y,
        {
            let d0 = y % 10;
            let d1 = (y / 10) % 10;
            let d2 = (y / 100) % 10;
            let d3 = (y / 1000) % 10;
            if d0 != d1 && d0 != d2 && d0 != d3 && d1 != d2 && d1 != d3 && d2 != d3 {
                proof {
                    lemma_distinct_digits_equiv(y as int, d0 as int, d1 as int, d2 as int, d3 as int);
                }
                return y;
            }
            proof {
                lemma_not_distinct_digits(y as int, d0 as int, d1 as int, d2 as int, d3 as int);
            }
            y += 1;
        }
        proof {
            
            
            if n <= 1022 {
                lemma_1023_beautiful();
                assert((n as int) < 1023 && 1023 < 10000);
                assert(!distinct_digits(1023));
                assert(false);
            } else {
                
                lemma_9012_beautiful();
                assert((n as int) < 9012 && 9012 < 10000);
                assert(!distinct_digits(9012));
                assert(false);
            }
        }
        y
    }
}

}