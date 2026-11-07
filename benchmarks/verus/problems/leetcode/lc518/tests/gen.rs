use vstd::prelude::*;

verus! {

pub open spec fn coin_change_ways(coins: Seq<i32>, coins_used: nat, amount: int) -> int
    decreases coins_used, amount,
{
    if coins_used == 0 {
        if amount == 0 {
            1
        } else {
            0
        }
    } else {
        let idx = (coins_used - 1) as int;
        let c = coins[idx] as int;
        coin_change_ways(coins, (coins_used - 1) as nat, amount)
            + (if 1 <= c <= amount {
                coin_change_ways(coins, coins_used, amount - c)
            } else {
                0
            })
    }
}

pub open spec fn ways_bounded(coins: Seq<i32>, amount: int, i: nat, j: int) -> bool {
    coin_change_ways(coins, i, j) <= 1073741823
}

proof fn lemma_ways_zero_coins(coins: Seq<i32>, a: int)
    ensures
        coin_change_ways(coins, 0, a) == (if a == 0 { 1int } else { 0int }),
{
}

// For 1 coin with value >= 1, ways is 0 or 1 for any non-negative amount.
proof fn lemma_ways_one_coin(coins: Seq<i32>, a: int)
    requires
        coins.len() >= 1,
        coins[0] >= 1,
        a >= 0,
    ensures
        coin_change_ways(coins, 1, a) >= 0,
        coin_change_ways(coins, 1, a) <= 1,
    decreases a,
{
    let c = coins[0] as int;
    lemma_ways_zero_coins(coins, a);
    if c > a {
    } else {
        lemma_ways_one_coin(coins, a - c);
    }
}

// For 2 coins each >= 1, ways <= a + 1 for any non-negative amount a.
proof fn lemma_ways_two_coins(coins: Seq<i32>, a: int)
    requires
        coins.len() >= 2,
        coins[0] >= 1,
        coins[1] >= 1,
        a >= 0,
    ensures
        coin_change_ways(coins, 2, a) >= 0,
        coin_change_ways(coins, 2, a) <= a + 1,
    decreases a,
{
    let c = coins[1] as int;
    lemma_ways_one_coin(coins, a);
    if c > a {
    } else {
        lemma_ways_two_coins(coins, a - c);
    }
}

pub fn generate_test_case(
    amount: i32,
    coin_val: i32,
    coin_val2: i32,
    mutation_kind: u8,
) -> (coins: Vec<i32>)
    requires
        0 <= amount <= 5000,
        1 <= coin_val <= 5000,
        1 <= coin_val2 <= 5000,
        coin_val != coin_val2,
    ensures
        0 <= amount <= 5000,
        1 <= coins.len() <= 300,
        forall|i: int| 0 <= i < coins.len() ==> 1 <= #[trigger] coins[i] <= 5000,
        forall|i: int, j: int| 0 <= i < j < coins.len() ==> coins[i] != coins[j],
        forall|i: nat, a: int|
            i <= (coins@).len() && 0 <= a <= amount as int
                ==> #[trigger] ways_bounded(coins@, amount as int, i, a),
{
    if mutation_kind <= 4 {
        // Single-coin constructions
        let cv: i32 = if mutation_kind == 0 {
            coin_val
        } else if mutation_kind == 1 {
            1i32
        } else if mutation_kind == 2 {
            5000i32
        } else if mutation_kind == 3 && coin_val < 5000 {
            (coin_val + 1) as i32
        } else if mutation_kind == 4 && coin_val > 1 {
            (coin_val - 1) as i32
        } else {
            coin_val
        };

        let mut coins: Vec<i32> = Vec::new();
        coins.push(cv);

        proof {
            assert forall|ii: nat, aa: int|
                ii <= (coins@).len() && 0 <= aa <= amount as int
                    implies #[trigger] ways_bounded(coins@, amount as int, ii, aa)
            by {
                if ii == 0 {
                } else {
                    lemma_ways_one_coin(coins@, aa);
                }
            }
        }

        coins
    } else {
        // Two-coin constructions
        let c1: i32 = if mutation_kind == 5 {
            coin_val
        } else if mutation_kind == 6 {
            coin_val2
        } else if mutation_kind == 7 && coin_val > 1 {
            1i32
        } else {
            coin_val
        };
        let c2: i32 = if mutation_kind == 5 {
            coin_val2
        } else if mutation_kind == 6 {
            coin_val
        } else if mutation_kind == 7 && coin_val > 1 {
            coin_val
        } else {
            coin_val2
        };

        assert(c1 != c2);

        let mut coins: Vec<i32> = Vec::new();
        coins.push(c1);
        coins.push(c2);

        proof {
            assert(coins@[0] == c1);
            assert(coins@[1] == c2);
            assert forall|ii: nat, aa: int|
                ii <= (coins@).len() && 0 <= aa <= amount as int
                    implies #[trigger] ways_bounded(coins@, amount as int, ii, aa)
            by {
                if ii == 0 {
                } else if ii == 1 {
                    lemma_ways_one_coin(coins@, aa);
                } else {
                    lemma_ways_two_coins(coins@, aa);
                }
            }
        }

        coins
    }
}

} // verus!

extern crate serde_json;
use serde_json::json;

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn main() {
    use std::io::Write;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(518);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut emitted = 0usize;

    let mut emit = |amount: i32, coins: Vec<i32>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    emitted: &mut usize| {
        let result = Solution::change(amount, coins.clone());
        writeln!(out, "{}", json!({
            "input": {"amount": amount, "coins": coins},
            "output": result
        })).unwrap();
        *emitted += 1;
    };

    // Examples from description.md
    emit(5, vec![1, 2, 5], &mut out, &mut emitted);
    emit(3, vec![2], &mut out, &mut emitted);
    emit(10, vec![10], &mut out, &mut emitted);

    // Boundary cases
    emit(0, vec![1], &mut out, &mut emitted);
    emit(0, vec![5000], &mut out, &mut emitted);
    emit(5000, vec![5000], &mut out, &mut emitted);
    emit(1, vec![1], &mut out, &mut emitted);
    emit(1, vec![2], &mut out, &mut emitted);
    emit(5000, vec![1], &mut out, &mut emitted);

    // Seed pools
    let coin_seeds: Vec<i32> = vec![1, 2, 5, 10, 25, 100, 1000, 5000];
    let amount_seeds: Vec<i32> = vec![0, 1, 5, 10, 100, 500, 1000, 5000];

    // Seed-based test cases with verified generator
    for &amt in &amount_seeds {
        for &cv in &coin_seeds {
            if emitted >= count { break; }
            let cv2 = if cv == 1 { 2i32 } else { 1i32 };
            let mk = rng.gen_range_usize(0, 7) as u8;
            let coins = generate_test_case(amt, cv, cv2, mk);
            emit(amt, coins, &mut out, &mut emitted);
        }
        if emitted >= count { break; }
    }

    // Random test cases with verified generator
    while emitted < count {
        let amount: i32 = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_i64(0, 10) as i32,
            1 => rng.gen_range_i64(0, 100) as i32,
            2 => rng.gen_range_i64(100, 1000) as i32,
            3 => rng.gen_range_i64(1000, 5000) as i32,
            _ => [0i64, 1, 5000, 4999, 2500][rng.gen_range_usize(0, 4)] as i32,
        };

        let cv1 = rng.gen_range_i64(1, 5000) as i32;
        let mut cv2 = rng.gen_range_i64(1, 5000) as i32;
        while cv2 == cv1 {
            cv2 = rng.gen_range_i64(1, 5000) as i32;
        }

        let mk = rng.gen_range_usize(0, 7) as u8;
        let coins = generate_test_case(amount, cv1, cv2, mk);
        emit(amount, coins, &mut out, &mut emitted);
    }
}
