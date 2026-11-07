use vstd::prelude::*;

verus! {

pub open spec fn to_int_seq(s: Seq<i32>) -> Seq<int> {
    s.map(|_idx: int, x: i32| x as int)
}

pub open spec fn count_above(s: Seq<int>, t: int) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 }
    else {
        count_above(s.drop_last(), t)
            + if s.last() > t { s.last() - t } else { 0 }
    }
}

proof fn to_int_seq_drop_last(s: Seq<i32>)
    requires s.len() > 0,
    ensures to_int_seq(s).drop_last() =~= to_int_seq(s.drop_last()),
{
    assert forall |i: int| 0 <= i < (s.len() - 1) implies
        to_int_seq(s).drop_last()[i] == to_int_seq(s.drop_last())[i]
    by {}
}

proof fn count_above_step(s: Seq<i32>, j: int)
    requires
        0 <= j < s.len(),
        forall |i: int| 0 <= i < s.len() ==> s[i] >= 1i32,
    ensures
        count_above(to_int_seq(s.subrange(0, j + 1)), 0)
            == count_above(to_int_seq(s.subrange(0, j)), 0) + s[j] as int,
{
    let sub = s.subrange(0, j + 1);
    assert(sub.drop_last() =~= s.subrange(0, j));
    to_int_seq_drop_last(sub);
    assert(to_int_seq(sub.drop_last()) =~= to_int_seq(s.subrange(0, j)));
    assert(to_int_seq(sub).last() == s[j] as int);
    assert(s[j] as int >= 1);
}

pub fn generate_test_case(
    inventory: Vec<i32>,
    orders_seed: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= inventory.len() <= 100_000,
        forall |i: int| 0 <= i < inventory.len() ==> 1 <= #[trigger] inventory[i] <= 1_000_000_000,
        1 <= orders_seed <= 1_000_000_000,
    ensures
        1 <= result.0.len() <= 100_000,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1_000_000_000,
        1 <= result.1 <= 1_000_000_000,
        result.1 as int <= count_above(to_int_seq(result.0@), 0),
{
    // Compute sum = count_above(to_int_seq(inventory@), 0)
    let mut sum: i64 = 0;
    let mut j: usize = 0;
    while j < inventory.len()
        invariant
            0 <= j <= inventory.len(),
            1 <= inventory.len() <= 100_000,
            forall |i: int| 0 <= i < inventory.len() ==> 1 <= #[trigger] inventory[i] <= 1_000_000_000,
            sum as int == count_above(to_int_seq(inventory@.subrange(0, j as int)), 0),
            j as int <= sum <= j as int * 1_000_000_000i64 as int,
        decreases inventory.len() - j,
    {
        proof {
            count_above_step(inventory@, j as int);
        }
        sum = sum + inventory[j] as i64;
        j = j + 1;
    }

    proof {
        assert(inventory@.subrange(0, inventory.len() as int) =~= inventory@);
        assert(to_int_seq(inventory@.subrange(0, inventory.len() as int))
            =~= to_int_seq(inventory@));
    }
    // Now: sum as int == count_above(to_int_seq(inventory@), 0)
    // And: sum >= inventory.len() >= 1

    let sum_capped: i64 = if sum > 1_000_000_000i64 { 1_000_000_000i64 } else { sum };
    // sum_capped >= 1 since sum >= 1

    let orders: i32 = if mutation_kind == 0 {
        // default: use orders_seed clamped to available
        if orders_seed as i64 <= sum_capped {
            orders_seed
        } else {
            sum_capped as i32
        }
    } else if mutation_kind == 1 {
        // minimum orders
        1i32
    } else if mutation_kind == 2 {
        // maximum orders (sell as many as allowed)
        sum_capped as i32
    } else if mutation_kind == 3 {
        // half of available
        let half = sum_capped / 2;
        if half >= 1 { half as i32 } else { 1i32 }
    } else if mutation_kind == 4 {
        // orders = inventory length
        let n = inventory.len() as i64;
        if n <= sum_capped { n as i32 } else { sum_capped as i32 }
    } else if mutation_kind == 5 {
        // quarter of available
        let quarter = sum_capped / 4;
        if quarter >= 1 { quarter as i32 } else { 1i32 }
    } else {
        // fallback: use orders_seed clamped
        if orders_seed as i64 <= sum_capped {
            orders_seed
        } else {
            sum_capped as i32
        }
    };

    (inventory, orders)
}

} // verus!

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

extern crate serde_json;
use serde_json::json;

fn random_inventory(rng: &mut Rng, len: usize, lo: i64, hi: i64) -> Vec<i32> {
    let mut inv = Vec::with_capacity(len);
    for _ in 0..len {
        inv.push(rng.gen_range_i64(lo, hi) as i32);
    }
    inv
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);
    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |inventory: Vec<i32>, orders: i32,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= target_count { return; }
        let key = format!("{:?}_{}", inventory, orders);
        if !seen.insert(key) { return; }
        let output = Solution::max_profit(inventory.clone(), orders);
        writeln!(out, "{}", json!({
            "input": {"inventory": inventory, "orders": orders},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    emit(vec![2, 5], 4, &mut seen, &mut out, &mut count);
    emit(vec![3, 5], 6, &mut seen, &mut out, &mut count);

    // Edge cases
    emit(vec![1], 1, &mut seen, &mut out, &mut count);
    emit(vec![1_000_000_000], 1, &mut seen, &mut out, &mut count);
    emit(vec![1_000_000_000], 1_000_000_000, &mut seen, &mut out, &mut count);
    emit(vec![1, 1], 1, &mut seen, &mut out, &mut count);
    emit(vec![1, 1], 2, &mut seen, &mut out, &mut count);
    emit(vec![1_000_000_000, 1_000_000_000], 1_000_000_000, &mut seen, &mut out, &mut count);

    // Interesting seed inventories with mutation_kinds
    let seeds: Vec<(Vec<i32>, i32)> = vec![
        (vec![2, 5], 4),
        (vec![3, 5], 6),
        (vec![1, 1, 1, 1, 1], 3),
        (vec![1_000_000_000, 1_000_000_000, 1_000_000_000], 1_000_000_000),
        (vec![1, 2, 3, 4, 5], 10),
        (vec![5, 4, 3, 2, 1], 5),
        (vec![100, 200, 300], 100),
        (vec![1_000_000_000], 500_000_000),
        (vec![500_000_000, 500_000_000], 1_000_000_000),
        (vec![1, 1_000_000_000], 999_999_999),
    ];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5];

    for (inv, ord) in &seeds {
        for &mk in &mutation_kinds {
            if count >= target_count { break; }
            let (result_inv, result_ord) = generate_test_case(inv.clone(), *ord, mk);
            emit(result_inv, result_ord, &mut seen, &mut out, &mut count);
        }
    }

    // Random test cases across size classes
    for i in 0..200 {
        if count >= target_count { break; }
        let n = match i % 5 {
            0 => rng.gen_range_usize(1, 3),          // tiny
            1 => rng.gen_range_usize(1, 10),         // small
            2 => rng.gen_range_usize(11, 100),        // medium
            3 => rng.gen_range_usize(101, 1000),      // large
            _ => rng.gen_range_usize(1001, 10_000),   // big
        };

        let val_range = match i % 4 {
            0 => (1i64, 10i64),                        // small values
            1 => (1i64, 1000i64),                      // medium values
            2 => (1i64, 1_000_000i64),                 // large values
            _ => (1i64, 1_000_000_000i64),             // full range
        };

        let inv = random_inventory(&mut rng, n, val_range.0, val_range.1);
        let sum: i64 = inv.iter().map(|&x| x as i64).sum();
        let max_orders = std::cmp::min(sum, 1_000_000_000) as i64;
        let orders_seed = rng.gen_range_i64(1, max_orders) as i32;
        let mk = rng.gen_range_usize(0, 5) as u8;

        let (result_inv, result_ord) = generate_test_case(inv, orders_seed, mk);
        emit(result_inv, result_ord, &mut seen, &mut out, &mut count);
    }

    // Fill remaining
    while count < target_count {
        let n = rng.gen_range_usize(1, 500);
        let inv = random_inventory(&mut rng, n, 1, 1_000_000_000);
        let sum: i64 = inv.iter().map(|&x| x as i64).sum();
        let max_orders = std::cmp::min(sum, 1_000_000_000) as i64;
        let orders_seed = rng.gen_range_i64(1, max_orders) as i32;
        let (result_inv, result_ord) = generate_test_case(inv, orders_seed, 0);
        emit(result_inv, result_ord, &mut seen, &mut out, &mut count);
    }
}
