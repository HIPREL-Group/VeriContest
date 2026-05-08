use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn catalan(n: int) -> int {
        if n == 0 { 1 }
        else if n == 1 { 1 }
        else if n == 2 { 2 }
        else if n == 3 { 5 }
        else if n == 4 { 14 }
        else if n == 5 { 42 }
        else if n == 6 { 132 }
        else if n == 7 { 429 }
        else if n == 8 { 1430 }
        else if n == 9 { 4862 }
        else if n == 10 { 16796 }
        else if n == 11 { 58786 }
        else if n == 12 { 208012 }
        else if n == 13 { 742900 }
        else if n == 14 { 2674440 }
        else if n == 15 { 9694845 }
        else if n == 16 { 35357670 }
        else if n == 17 { 129644790 }
        else if n == 18 { 477638700 }
        else if n == 19 { 1767263190 }
        else { 0 }
    }

    pub open spec fn catalan_partial_sum(n: int, k: int) -> int
        decreases k
    {
        if k <= 0 {
            0
        } else {
            Solution::catalan(k - 1) * Solution::catalan(n - k)
                + Solution::catalan_partial_sum(n, k - 1)
        }
    }

    proof fn catalan_partial_sum_mono(n: int, k1: int, k2: int)
        requires
            2 <= n <= 19,
            0 <= k1 <= k2 <= n,
        ensures
            Solution::catalan_partial_sum(n, k1) <= Solution::catalan_partial_sum(n, k2),
        decreases k2 - k1,
    {
        if k1 == k2 {
        } else {
            Solution::catalan_partial_sum_mono(n, k1, k2 - 1);
            reveal_with_fuel(Solution::catalan_partial_sum, 2);
        }
    }

    proof fn catalan_partial_sum_eq(n: int)
        requires
            2 <= n <= 19,
        ensures
            Solution::catalan_partial_sum(n, n) == Solution::catalan(n),
    {
        if n == 2 {
            assert(Solution::catalan_partial_sum(2, 1) == 1) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(Solution::catalan_partial_sum(2, 2) == 2) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
        } else if n == 3 {
            assert(Solution::catalan_partial_sum(3, 1) == 2) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(Solution::catalan_partial_sum(3, 2) == 3) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(Solution::catalan_partial_sum(3, 3) == 5) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
        } else if n == 4 {
            assert(Solution::catalan_partial_sum(4, 1) == 5) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(Solution::catalan_partial_sum(4, 2) == 7) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(Solution::catalan_partial_sum(4, 3) == 9) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(Solution::catalan_partial_sum(4, 4) == 14) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
        } else if n == 5 {
            assert(Solution::catalan_partial_sum(5, 1) == 14) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(Solution::catalan_partial_sum(5, 2) == 19) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(Solution::catalan_partial_sum(5, 3) == 23) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(Solution::catalan_partial_sum(5, 4) == 28) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(Solution::catalan_partial_sum(5, 5) == 42) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
        } else if n == 6 {
            assert(Solution::catalan_partial_sum(6, 1) == 42) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(Solution::catalan_partial_sum(6, 2) == 56) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(Solution::catalan_partial_sum(6, 3) == 66) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(Solution::catalan_partial_sum(6, 4) == 76) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(Solution::catalan_partial_sum(6, 5) == 90) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(Solution::catalan_partial_sum(6, 6) == 132) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
        } else if n == 7 {
            assert(Solution::catalan_partial_sum(7, 1) == 132) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(Solution::catalan_partial_sum(7, 2) == 174) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(Solution::catalan_partial_sum(7, 3) == 202) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(Solution::catalan_partial_sum(7, 4) == 227) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(Solution::catalan_partial_sum(7, 5) == 255) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(Solution::catalan_partial_sum(7, 6) == 297) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(Solution::catalan_partial_sum(7, 7) == 429) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
        } else if n == 8 {
            assert(Solution::catalan_partial_sum(8, 1) == 429) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(Solution::catalan_partial_sum(8, 2) == 561) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(2 * 42 == 84);
            assert(Solution::catalan_partial_sum(8, 3) == 645) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(5 * 14 == 70);
            assert(Solution::catalan_partial_sum(8, 4) == 715) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(14 * 5 == 70);
            assert(Solution::catalan_partial_sum(8, 5) == 785) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(42 * 2 == 84);
            assert(Solution::catalan_partial_sum(8, 6) == 869) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(132 * 1 == 132);
            assert(Solution::catalan_partial_sum(8, 7) == 1001) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(429 * 1 == 429);
            assert(Solution::catalan_partial_sum(8, 8) == 1430) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
        } else if n == 9 {
            assert(1 * 1430 == 1430);
            assert(Solution::catalan_partial_sum(9, 1) == 1430) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(1 * 429 == 429);
            assert(Solution::catalan_partial_sum(9, 2) == 1859) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(2 * 132 == 264);
            assert(Solution::catalan_partial_sum(9, 3) == 2123) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(5 * 42 == 210);
            assert(Solution::catalan_partial_sum(9, 4) == 2333) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(14 * 14 == 196);
            assert(Solution::catalan_partial_sum(9, 5) == 2529) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(42 * 5 == 210);
            assert(Solution::catalan_partial_sum(9, 6) == 2739) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(132 * 2 == 264);
            assert(Solution::catalan_partial_sum(9, 7) == 3003) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(429 * 1 == 429);
            assert(Solution::catalan_partial_sum(9, 8) == 3432) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(1430 * 1 == 1430);
            assert(Solution::catalan_partial_sum(9, 9) == 4862) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
        } else if n == 10 {
            assert(1 * 4862 == 4862);
            assert(Solution::catalan_partial_sum(10, 1) == 4862) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(1 * 1430 == 1430);
            assert(Solution::catalan_partial_sum(10, 2) == 6292) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(2 * 429 == 858);
            assert(Solution::catalan_partial_sum(10, 3) == 7150) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(5 * 132 == 660);
            assert(Solution::catalan_partial_sum(10, 4) == 7810) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(14 * 42 == 588);
            assert(Solution::catalan_partial_sum(10, 5) == 8398) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(42 * 14 == 588);
            assert(Solution::catalan_partial_sum(10, 6) == 8986) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(132 * 5 == 660);
            assert(Solution::catalan_partial_sum(10, 7) == 9646) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(429 * 2 == 858);
            assert(Solution::catalan_partial_sum(10, 8) == 10504) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(1430 * 1 == 1430);
            assert(Solution::catalan_partial_sum(10, 9) == 11934) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(4862 * 1 == 4862);
            assert(Solution::catalan_partial_sum(10, 10) == 16796) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
        } else if n == 11 {
            assert(1 * 16796 == 16796);
            assert(Solution::catalan_partial_sum(11, 1) == 16796) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(1 * 4862 == 4862);
            assert(Solution::catalan_partial_sum(11, 2) == 21658) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(2 * 1430 == 2860);
            assert(Solution::catalan_partial_sum(11, 3) == 24518) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(5 * 429 == 2145);
            assert(Solution::catalan_partial_sum(11, 4) == 26663) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(14 * 132 == 1848);
            assert(Solution::catalan_partial_sum(11, 5) == 28511) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(42 * 42 == 1764);
            assert(Solution::catalan_partial_sum(11, 6) == 30275) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(132 * 14 == 1848);
            assert(Solution::catalan_partial_sum(11, 7) == 32123) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(429 * 5 == 2145);
            assert(Solution::catalan_partial_sum(11, 8) == 34268) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(1430 * 2 == 2860);
            assert(Solution::catalan_partial_sum(11, 9) == 37128) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(4862 * 1 == 4862);
            assert(Solution::catalan_partial_sum(11, 10) == 41990) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(16796 * 1 == 16796);
            assert(Solution::catalan_partial_sum(11, 11) == 58786) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
        } else if n == 12 {
            assert(1 * 58786 == 58786);
            assert(Solution::catalan_partial_sum(12, 1) == 58786) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(1 * 16796 == 16796);
            assert(Solution::catalan_partial_sum(12, 2) == 75582) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(2 * 4862 == 9724);
            assert(Solution::catalan_partial_sum(12, 3) == 85306) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(5 * 1430 == 7150);
            assert(Solution::catalan_partial_sum(12, 4) == 92456) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(14 * 429 == 6006);
            assert(Solution::catalan_partial_sum(12, 5) == 98462) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(42 * 132 == 5544);
            assert(Solution::catalan_partial_sum(12, 6) == 104006) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(132 * 42 == 5544);
            assert(Solution::catalan_partial_sum(12, 7) == 109550) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(429 * 14 == 6006);
            assert(Solution::catalan_partial_sum(12, 8) == 115556) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(1430 * 5 == 7150);
            assert(Solution::catalan_partial_sum(12, 9) == 122706) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(4862 * 2 == 9724);
            assert(Solution::catalan_partial_sum(12, 10) == 132430) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(16796 * 1 == 16796);
            assert(Solution::catalan_partial_sum(12, 11) == 149226) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(58786 * 1 == 58786);
            assert(Solution::catalan_partial_sum(12, 12) == 208012) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
        } else if n == 13 {
            assert(1 * 208012 == 208012);
            assert(Solution::catalan_partial_sum(13, 1) == 208012) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(1 * 58786 == 58786);
            assert(Solution::catalan_partial_sum(13, 2) == 266798) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(2 * 16796 == 33592);
            assert(Solution::catalan_partial_sum(13, 3) == 300390) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(5 * 4862 == 24310);
            assert(Solution::catalan_partial_sum(13, 4) == 324700) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(14 * 1430 == 20020);
            assert(Solution::catalan_partial_sum(13, 5) == 344720) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(42 * 429 == 18018);
            assert(Solution::catalan_partial_sum(13, 6) == 362738) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(132 * 132 == 17424);
            assert(Solution::catalan_partial_sum(13, 7) == 380162) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(429 * 42 == 18018);
            assert(Solution::catalan_partial_sum(13, 8) == 398180) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(1430 * 14 == 20020);
            assert(Solution::catalan_partial_sum(13, 9) == 418200) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(4862 * 5 == 24310);
            assert(Solution::catalan_partial_sum(13, 10) == 442510) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(16796 * 2 == 33592);
            assert(Solution::catalan_partial_sum(13, 11) == 476102) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(58786 * 1 == 58786);
            assert(Solution::catalan_partial_sum(13, 12) == 534888) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(208012 * 1 == 208012);
            assert(Solution::catalan_partial_sum(13, 13) == 742900) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
        } else if n == 14 {
            assert(1 * 742900 == 742900);
            assert(Solution::catalan_partial_sum(14, 1) == 742900) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(1 * 208012 == 208012);
            assert(Solution::catalan_partial_sum(14, 2) == 950912) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(2 * 58786 == 117572);
            assert(Solution::catalan_partial_sum(14, 3) == 1068484) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(5 * 16796 == 83980);
            assert(Solution::catalan_partial_sum(14, 4) == 1152464) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(14 * 4862 == 68068);
            assert(Solution::catalan_partial_sum(14, 5) == 1220532) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(42 * 1430 == 60060);
            assert(Solution::catalan_partial_sum(14, 6) == 1280592) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(132 * 429 == 56628);
            assert(Solution::catalan_partial_sum(14, 7) == 1337220) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(429 * 132 == 56628);
            assert(Solution::catalan_partial_sum(14, 8) == 1393848) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(1430 * 42 == 60060);
            assert(Solution::catalan_partial_sum(14, 9) == 1453908) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(4862 * 14 == 68068);
            assert(Solution::catalan_partial_sum(14, 10) == 1521976) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(16796 * 5 == 83980);
            assert(Solution::catalan_partial_sum(14, 11) == 1605956) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(58786 * 2 == 117572);
            assert(Solution::catalan_partial_sum(14, 12) == 1723528) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(208012 * 1 == 208012);
            assert(Solution::catalan_partial_sum(14, 13) == 1931540) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(742900 * 1 == 742900);
            assert(Solution::catalan_partial_sum(14, 14) == 2674440) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
        } else if n == 15 {
            assert(1 * 2674440 == 2674440);
            assert(Solution::catalan_partial_sum(15, 1) == 2674440) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(1 * 742900 == 742900);
            assert(Solution::catalan_partial_sum(15, 2) == 3417340) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(2 * 208012 == 416024);
            assert(Solution::catalan_partial_sum(15, 3) == 3833364) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(5 * 58786 == 293930);
            assert(Solution::catalan_partial_sum(15, 4) == 4127294) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(14 * 16796 == 235144);
            assert(Solution::catalan_partial_sum(15, 5) == 4362438) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(42 * 4862 == 204204);
            assert(Solution::catalan_partial_sum(15, 6) == 4566642) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(132 * 1430 == 188760);
            assert(Solution::catalan_partial_sum(15, 7) == 4755402) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(429 * 429 == 184041);
            assert(Solution::catalan_partial_sum(15, 8) == 4939443) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(1430 * 132 == 188760);
            assert(Solution::catalan_partial_sum(15, 9) == 5128203) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(4862 * 42 == 204204);
            assert(Solution::catalan_partial_sum(15, 10) == 5332407) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(16796 * 14 == 235144);
            assert(Solution::catalan_partial_sum(15, 11) == 5567551) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(58786 * 5 == 293930);
            assert(Solution::catalan_partial_sum(15, 12) == 5861481) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(208012 * 2 == 416024);
            assert(Solution::catalan_partial_sum(15, 13) == 6277505) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(742900 * 1 == 742900);
            assert(Solution::catalan_partial_sum(15, 14) == 7020405) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(2674440 * 1 == 2674440);
            assert(Solution::catalan_partial_sum(15, 15) == 9694845) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
        } else if n == 16 {
            assert(1 * 9694845 == 9694845);
            assert(Solution::catalan_partial_sum(16, 1) == 9694845) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(1 * 2674440 == 2674440);
            assert(Solution::catalan_partial_sum(16, 2) == 12369285) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(2 * 742900 == 1485800);
            assert(Solution::catalan_partial_sum(16, 3) == 13855085) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(5 * 208012 == 1040060);
            assert(Solution::catalan_partial_sum(16, 4) == 14895145) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(14 * 58786 == 823004);
            assert(Solution::catalan_partial_sum(16, 5) == 15718149) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(42 * 16796 == 705432);
            assert(Solution::catalan_partial_sum(16, 6) == 16423581) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(132 * 4862 == 641784);
            assert(Solution::catalan_partial_sum(16, 7) == 17065365) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(429 * 1430 == 613470);
            assert(Solution::catalan_partial_sum(16, 8) == 17678835) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(1430 * 429 == 613470);
            assert(Solution::catalan_partial_sum(16, 9) == 18292305) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(4862 * 132 == 641784);
            assert(Solution::catalan_partial_sum(16, 10) == 18934089) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(16796 * 42 == 705432);
            assert(Solution::catalan_partial_sum(16, 11) == 19639521) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(58786 * 14 == 823004);
            assert(Solution::catalan_partial_sum(16, 12) == 20462525) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(208012 * 5 == 1040060);
            assert(Solution::catalan_partial_sum(16, 13) == 21502585) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(742900 * 2 == 1485800);
            assert(Solution::catalan_partial_sum(16, 14) == 22988385) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(2674440 * 1 == 2674440);
            assert(Solution::catalan_partial_sum(16, 15) == 25662825) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(9694845 * 1 == 9694845);
            assert(Solution::catalan_partial_sum(16, 16) == 35357670) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
        } else if n == 17 {
            assert(1 * 35357670 == 35357670);
            assert(Solution::catalan_partial_sum(17, 1) == 35357670) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(1 * 9694845 == 9694845);
            assert(Solution::catalan_partial_sum(17, 2) == 45052515) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(2 * 2674440 == 5348880);
            assert(Solution::catalan_partial_sum(17, 3) == 50401395) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(5 * 742900 == 3714500);
            assert(Solution::catalan_partial_sum(17, 4) == 54115895) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(14 * 208012 == 2912168);
            assert(Solution::catalan_partial_sum(17, 5) == 57028063) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(42 * 58786 == 2469012);
            assert(Solution::catalan_partial_sum(17, 6) == 59497075) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(132 * 16796 == 2217072);
            assert(Solution::catalan_partial_sum(17, 7) == 61714147) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(429 * 4862 == 2085798);
            assert(Solution::catalan_partial_sum(17, 8) == 63799945) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(1430 * 1430 == 2044900);
            assert(Solution::catalan_partial_sum(17, 9) == 65844845) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(4862 * 429 == 2085798);
            assert(Solution::catalan_partial_sum(17, 10) == 67930643) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(16796 * 132 == 2217072);
            assert(Solution::catalan_partial_sum(17, 11) == 70147715) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(58786 * 42 == 2469012);
            assert(Solution::catalan_partial_sum(17, 12) == 72616727) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(208012 * 14 == 2912168);
            assert(Solution::catalan_partial_sum(17, 13) == 75528895) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(742900 * 5 == 3714500);
            assert(Solution::catalan_partial_sum(17, 14) == 79243395) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(2674440 * 2 == 5348880);
            assert(Solution::catalan_partial_sum(17, 15) == 84592275) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(9694845 * 1 == 9694845);
            assert(Solution::catalan_partial_sum(17, 16) == 94287120) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(35357670 * 1 == 35357670);
            assert(Solution::catalan_partial_sum(17, 17) == 129644790) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
        } else if n == 18 {
            assert(1 * 129644790 == 129644790);
            assert(Solution::catalan_partial_sum(18, 1) == 129644790) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(1 * 35357670 == 35357670);
            assert(Solution::catalan_partial_sum(18, 2) == 165002460) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(2 * 9694845 == 19389690);
            assert(Solution::catalan_partial_sum(18, 3) == 184392150) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(5 * 2674440 == 13372200);
            assert(Solution::catalan_partial_sum(18, 4) == 197764350) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(14 * 742900 == 10400600);
            assert(Solution::catalan_partial_sum(18, 5) == 208164950) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(42 * 208012 == 8736504);
            assert(Solution::catalan_partial_sum(18, 6) == 216901454) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(132 * 58786 == 7759752);
            assert(Solution::catalan_partial_sum(18, 7) == 224661206) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(429 * 16796 == 7205484);
            assert(Solution::catalan_partial_sum(18, 8) == 231866690) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(1430 * 4862 == 6952660);
            assert(Solution::catalan_partial_sum(18, 9) == 238819350) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(4862 * 1430 == 6952660);
            assert(Solution::catalan_partial_sum(18, 10) == 245772010) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(16796 * 429 == 7205484);
            assert(Solution::catalan_partial_sum(18, 11) == 252977494) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(58786 * 132 == 7759752);
            assert(Solution::catalan_partial_sum(18, 12) == 260737246) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(208012 * 42 == 8736504);
            assert(Solution::catalan_partial_sum(18, 13) == 269473750) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(742900 * 14 == 10400600);
            assert(Solution::catalan_partial_sum(18, 14) == 279874350) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(2674440 * 5 == 13372200);
            assert(Solution::catalan_partial_sum(18, 15) == 293246550) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(9694845 * 2 == 19389690);
            assert(Solution::catalan_partial_sum(18, 16) == 312636240) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(35357670 * 1 == 35357670);
            assert(Solution::catalan_partial_sum(18, 17) == 347993910) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(129644790 * 1 == 129644790);
            assert(Solution::catalan_partial_sum(18, 18) == 477638700) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
        } else {
            assert(1 * 477638700 == 477638700);
            assert(Solution::catalan_partial_sum(19, 1) == 477638700) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(1 * 129644790 == 129644790);
            assert(Solution::catalan_partial_sum(19, 2) == 607283490) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(2 * 35357670 == 70715340);
            assert(Solution::catalan_partial_sum(19, 3) == 677998830) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(5 * 9694845 == 48474225);
            assert(Solution::catalan_partial_sum(19, 4) == 726473055) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(14 * 2674440 == 37442160);
            assert(Solution::catalan_partial_sum(19, 5) == 763915215) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(42 * 742900 == 31201800);
            assert(Solution::catalan_partial_sum(19, 6) == 795117015) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(132 * 208012 == 27457584);
            assert(Solution::catalan_partial_sum(19, 7) == 822574599) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(429 * 58786 == 25219194);
            assert(Solution::catalan_partial_sum(19, 8) == 847793793) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(1430 * 16796 == 24018280);
            assert(Solution::catalan_partial_sum(19, 9) == 871812073) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(4862 * 4862 == 23639044);
            assert(Solution::catalan_partial_sum(19, 10) == 895451117) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(16796 * 1430 == 24018280);
            assert(Solution::catalan_partial_sum(19, 11) == 919469397) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(58786 * 429 == 25219194);
            assert(Solution::catalan_partial_sum(19, 12) == 944688591) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(208012 * 132 == 27457584);
            assert(Solution::catalan_partial_sum(19, 13) == 972146175) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(742900 * 42 == 31201800);
            assert(Solution::catalan_partial_sum(19, 14) == 1003347975) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(2674440 * 14 == 37442160);
            assert(Solution::catalan_partial_sum(19, 15) == 1040790135) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(9694845 * 5 == 48474225);
            assert(Solution::catalan_partial_sum(19, 16) == 1089264360) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(35357670 * 2 == 70715340);
            assert(Solution::catalan_partial_sum(19, 17) == 1159979700) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(129644790 * 1 == 129644790);
            assert(Solution::catalan_partial_sum(19, 18) == 1289624490) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
            assert(477638700 * 1 == 477638700);
            assert(Solution::catalan_partial_sum(19, 19) == 1767263190) by { reveal_with_fuel(Solution::catalan_partial_sum, 2); };
        }
    }

    proof fn catalan_partial_sum_bounded(n: int, k: int)
        requires
            2 <= n <= 19,
            0 <= k <= n,
        ensures
            Solution::catalan_partial_sum(n, k) <= Solution::catalan(n),
    {
        Solution::catalan_partial_sum_mono(n, k, n);
        Solution::catalan_partial_sum_eq(n);
    }

    proof fn catalan_partial_sum_nonneg(n: int, k: int)
        requires
            2 <= n <= 19,
            0 <= k <= n,
        ensures
            0 <= Solution::catalan_partial_sum(n, k),
    {
        Solution::catalan_partial_sum_mono(n, 0, k);
        assert(Solution::catalan_partial_sum(n, 0) == 0) by {
            reveal_with_fuel(Solution::catalan_partial_sum, 2);
        };
    }

    pub fn num_trees(n: i32) -> (result: i32)
        requires
            1 <= n <= 19,
        ensures
            result as int == Solution::catalan(n as int),
    {
        let mut dp: Vec<i32> = Vec::new();
        dp.push(1i32);
        dp.push(1i32);

        let mut i: usize = 2;
        while i <= n as usize
            invariant
                1 <= n <= 19,
                2 <= i,
                i <= n as usize + 1,
                dp.len() == i,
                forall |k: int| #![auto] 0 <= k < i as int ==> dp@[k] as int == Solution::catalan(k),
            decreases n as usize + 1 - i,
        {
            let mut sum: i32 = 0;
            let mut j: usize = 0;

            proof {
                assert(Solution::catalan_partial_sum(i as int, 0) == 0) by {
                    reveal_with_fuel(Solution::catalan_partial_sum, 2);
                };
                Solution::catalan_partial_sum_nonneg(i as int, 0);
            }

            while j < i
                invariant
                    2 <= i <= 19,
                    j <= i,
                    dp.len() == i,
                    0 <= sum,
                    sum as int == Solution::catalan_partial_sum(i as int, j as int),
                    forall |k: int| #![auto] 0 <= k < i as int ==> dp@[k] as int == Solution::catalan(k),
                decreases i - j,
            {
                let dj = dp[j];
                let dimj = dp[i - 1 - j];

                proof {
                    let i_int = i as int;
                    let j_int = j as int;

                    reveal_with_fuel(Solution::catalan_partial_sum, 2);
                    assert(Solution::catalan_partial_sum(i_int, j_int + 1) ==
                        Solution::catalan(j_int) * Solution::catalan(i_int - 1 - j_int)
                        + Solution::catalan_partial_sum(i_int, j_int));
                    assert(dj as int == Solution::catalan(j_int));
                    assert(dimj as int == Solution::catalan(i_int - 1 - j_int));
                    Solution::catalan_partial_sum_bounded(i_int, j_int + 1);
                    assert(Solution::catalan_partial_sum(i_int, j_int + 1) <= Solution::catalan(i_int));
                    assert(sum as int + dj as int * dimj as int ==
                        Solution::catalan_partial_sum(i_int, j_int + 1));
                    Solution::catalan_partial_sum_nonneg(i_int, j_int);
                }

                sum = sum + dj * dimj;
                j = j + 1;
            }

            proof {
                Solution::catalan_partial_sum_eq(i as int);
            }

            dp.push(sum);
            i = i + 1;
        }

        proof {
            let k = n as int;
            assert(dp@[k] as int == Solution::catalan(k));
        }

        dp[n as usize]
    }
}

} 
