use vstd::prelude::*;

fn main() {}

verus! {
    pub struct Solution;

    impl Solution {
        pub fn minimum_card_pickup(cards: Vec<i32>) -> (res: i32)
            requires
                1 <= cards.len() <= 100000,
                forall|i: int| 0 <= i < cards.len() ==> 0 <= #[trigger] cards[i] <= 1000000,
            ensures
                res == -1 ==> (forall|i: int, j: int| 0 <= i < j < cards.len() as int ==> #[trigger] cards[i] != #[trigger] cards[j]),
                res != -1 ==> (exists|i: int, j: int| 0 <= i < j < cards.len() as int && #[trigger] cards[i] == #[trigger] cards[j] && res as int == j - i + 1),
                res != -1 ==> (forall|i: int, j: int| 0 <= i < j < cards.len() as int && #[trigger] cards[i] == #[trigger] cards[j] ==> res as int <= j - i + 1),
        {
            let mut min_pickup = i32::MAX;
            let n = cards.len();
            assert(n == cards.len());
            assert(n <= 100000usize);
            
            let mut i: usize = 0;
            while i < n
                invariant
                    i <= n,
                    n == cards.len(),
                    n >= 1,
                    n <= 100000,
                    forall|k: int| 0 <= k < n as int ==> 0 <= #[trigger] cards[k] <= 1000000,
                    min_pickup == i32::MAX ==> (forall|a: int, b: int| 0 <= a < i as int && a < b < n as int ==> #[trigger] cards[a] != #[trigger] cards[b]),
                    min_pickup != i32::MAX ==> (2 <= min_pickup as int <= n as int),
                    min_pickup != i32::MAX ==> (exists|a: int, b: int| 0 <= a < i as int && a < b < n as int && #[trigger] cards[a] == #[trigger] cards[b] && min_pickup as int == b - a + 1),
                    min_pickup != i32::MAX ==> (forall|a: int, b: int| 0 <= a < i as int && a < b < n as int && #[trigger] cards[a] == #[trigger] cards[b] ==> min_pickup as int <= b - a + 1),
                decreases n - i
            {
                let ghost pre_min: int = min_pickup as int;
                let ghost mut found: bool = false;
                let ghost mut found_at: int = 0;

                let mut j: usize = i + 1;
                while j < n
                    invariant
                        i < n,
                        i + 1 <= j <= n,
                        n == cards.len(),
                        n <= 100000,
                        forall|k: int| 0 <= k < n as int ==> 0 <= #[trigger] cards[k] <= 1000000,
                        pre_min == i32::MAX as int || (2 <= pre_min <= n as int),
                        !found ==> (
                            min_pickup as int == pre_min
                            && forall|b: int| (i as int + 1) <= b < j as int ==> cards[i as int] != #[trigger] cards[b]
                        ),
                        found ==> i as int + 1 <= found_at,
                        found ==> found_at < n as int,
                        found ==> cards[i as int] == cards[found_at],
                        found ==> j == n,
                        found ==> (forall|b: int| (i as int + 1) <= b < found_at ==> cards[i as int] != #[trigger] cards[b]),
                        found ==> min_pickup as int <= pre_min,
                        found ==> min_pickup as int <= found_at - i as int + 1,
                        found ==> (min_pickup as int == found_at - i as int + 1 || min_pickup as int == pre_min),
                    decreases n - j
                {
                    if cards[i] == cards[j] {
                        assert(j - i + 1 <= n);
                        let pickup = (j - i + 1) as i32;
                        if pickup < min_pickup {
                            min_pickup = pickup;
                        }
                        proof {
                            found = true;
                            found_at = j as int;
                        }
                        j = n;
                    } else {
                        j = j + 1;
                    }
                }

                proof {
                    if found {
                        assert(cards[i as int] == cards[found_at]);
                        assert(i as int + 1 <= found_at && found_at < n as int);
                        assert(min_pickup as int <= found_at - i as int + 1);
                        assert(min_pickup as int <= pre_min);

                        // For any b matching cards[i], b >= found_at
                        assert forall|b: int| i as int + 1 <= b < n as int && cards[i as int] == #[trigger] cards[b]
                            implies min_pickup as int <= b - i as int + 1
                        by {
                            if b < found_at {
                                assert((i as int + 1) <= b && b < found_at);
                                assert(cards[i as int] != cards[b]);
                            } else {
                                assert(b >= found_at);
                                assert(b - i as int + 1 >= found_at - i as int + 1);
                            }
                        };

                        // Exists witness
                        if min_pickup as int == found_at - i as int + 1 {
                            assert(0 <= i as int && (i as int) < found_at && found_at < n as int);
                            assert(#[trigger] cards[i as int] == #[trigger] cards[found_at]);
                        }

                        // Minimality for all pairs with a < i + 1
                        assert forall|a: int, b: int| 0 <= a < i as int + 1 && a < b < n as int && #[trigger] cards[a] == #[trigger] cards[b]
                            implies min_pickup as int <= b - a + 1
                        by {
                            if a < i as int {
                                // outer invariant: pre_min <= b - a + 1, and min_pickup <= pre_min
                            } else {
                                assert(a == i as int);
                                if b < found_at {
                                    assert((i as int + 1) <= b && b < found_at);
                                    assert(cards[i as int] != cards[b]);
                                } else {
                                    assert(b >= found_at);
                                    assert(b - a + 1 >= found_at - i as int + 1);
                                }
                            }
                        };
                    } else {
                        assert(forall|b: int| (i as int + 1) <= b < n as int ==> cards[i as int] != #[trigger] cards[b]);
                        assert(min_pickup as int == pre_min);

                        if min_pickup == i32::MAX {
                            assert forall|a: int, b: int| 0 <= a < i as int + 1 && a < b < n as int
                                implies #[trigger] cards[a] != #[trigger] cards[b]
                            by {
                                if a < i as int {
                                } else {
                                    assert(a == i as int);
                                    assert((i as int + 1) <= b && b < n as int);
                                    assert(cards[i as int] != cards[b]);
                                }
                            };
                        }
                    }
                }

                i = i + 1;
            }
            
            if min_pickup == i32::MAX {
                -1
            } else {
                min_pickup
            }
        }
    }
}
