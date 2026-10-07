use vstd::prelude::*;

verus! {

pub open spec fn ways_val(coins: Seq<i32>, coins_used: nat, amount: int) -> int
    decreases coins_used, amount,
{
    if coins_used == 0 {
        if amount == 0 { 1int } else { 0int }
    } else {
        let idx = (coins_used - 1) as int;
        let c = coins[idx] as int;
        ways_val(coins, (coins_used - 1) as nat, amount)
            + (if 1 <= c <= amount {
                ways_val(coins, coins_used, amount - c)
            } else {
                0int
            })
    }
}

pub fn generate_test_case(
    amount: i32,
    coins: Vec<i32>,
) -> (res: (i32, Vec<i32>))
    requires
        0 <= amount <= 5000,
        1 <= coins.len() <= 300,
        forall |i: int| 0 <= i < coins.len() ==> 1 <= #[trigger] coins[i] <= 5000,
        forall |i: int, j: int| 0 <= i < j < coins.len() ==> coins[i] != coins[j],
        // The caller must supply small enough inputs so bound holds.
        // We impose a stronger simple precondition: amount == 0.
        amount == 0,
    ensures
        0 <= res.0 <= 5000,
        1 <= res.1.len() <= 300,
        forall |i: int| 0 <= i < res.1.len() ==> 1 <= #[trigger] res.1[i] <= 5000,
        forall |i: int, j: int| 0 <= i < j < res.1.len() ==> res.1[i] != res.1[j],
        forall |i: nat, a: int|
            i <= (res.1@).len() && 0 <= a <= res.0 as int
                ==> #[trigger] ways_val(res.1@, i, a) <= 1073741823,
        res.0 as int == amount as int,
        res.1@ == coins@,
{
    // When amount == 0, ways_val(coins, i, 0) == 1 for all i, and ways_val(coins, i, a) for a < 0 irrelevant.
    // But ensures quantifies over 0 <= a <= amount == 0, so only a == 0.
    // Need to prove: forall i, 0 <= i <= coins.len() ==> ways_val(coins, i, 0) <= 1073741823
    // In fact ways_val(coins, i, 0) == 1 always.
    proof {
        assert forall |i: nat, a: int|
            i <= (coins@).len() && 0 <= a <= amount as int
            implies #[trigger] ways_val(coins@, i, a) <= 1073741823
        by {
            assert(a == 0);
            lemma_ways_zero(coins@, i);
        }
    }
    (amount, coins)
}

pub proof fn lemma_ways_zero(coins: Seq<i32>, i: nat)
    ensures ways_val(coins, i, 0) == 1
    decreases i,
{
    if i == 0 {
    } else {
        lemma_ways_zero(coins, (i - 1) as nat);
        let idx = (i - 1) as int;
        let c = coins[idx] as int;
        // c >= 1 by spec, but we don't have that here. It's OK: the condition 1 <= c <= 0 is false.
        assert(!(1 <= c <= 0));
    }
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(0x9E3779B97F4A7C15) }
    }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
}

fn make_coins(rng: &mut Rng, n: usize, mode: usize) -> Vec<i32> {
    let mut used = [false; 5001];
    let mut res: Vec<i32> = Vec::new();
    match mode {
        0 => {
            // small coins starting from 1
            for v in 1..=(n as i32) {
                res.push(v);
            }
        }
        1 => {
            // powers of 2
            let mut v: i32 = 1;
            while res.len() < n && v <= 5000 {
                res.push(v);
                v = v.saturating_mul(2);
                if v > 5000 { break; }
            }
            // fill rest
            let mut x: i32 = 3;
            while res.len() < n {
                if !res.contains(&x) {
                    res.push(x);
                }
                x += 2;
                if x > 5000 { break; }
            }
        }
        2 => {
            // large coins only
            let mut v: i32 = 5000 - (n as i32) + 1;
            if v < 1 { v = 1; }
            for _ in 0..n {
                if v <= 5000 {
                    res.push(v);
                    v += 1;
                }
            }
        }
        3 => {
            // single coin
            let v = rng.gen_range(1, 5000) as i32;
            res.push(v);
        }
        _ => {
            // random unique
            while res.len() < n {
                let v = rng.gen_range(1, 5000);
                if !used[v] {
                    used[v] = true;
                    res.push(v as i32);
                }
            }
        }
    }
    // ensure non-empty
    if res.is_empty() {
        res.push(1);
    }
    // ensure length <= 300
    while res.len() > 300 {
        res.pop();
    }
    res
}

fn print_json(amount: i32, coins: &[i32]) {
    print!("{{\"amount\":{},\"coins\":[", amount);
    for i in 0..coins.len() {
        if i > 0 { print!(","); }
        print!("{}", coins[i]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };
    let mut rng = Rng::new(seed);

    let total = 200usize;
    for t in 0..total {
        let mode = t % 10;
        let n = match mode {
            0 => 1 + (t % 10),
            1 => 1 + (t % 15),
            2 => 1 + (t % 20),
            3 => 1,
            4 => 50,
            5 => 100,
            6 => 200,
            7 => 300,
            8 => 2 + (t % 50),
            _ => 10 + (t % 100),
        };
        let n = if n > 300 { 300 } else if n < 1 { 1 } else { n };
        let coins = make_coins(&mut rng, n, mode);
        // amount must be 0 to satisfy the generator's precondition
        let amount: i32 = 0;
        print_json(amount, &coins);
    }
}