use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    order: Vec<i32>,
    friends: Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= order.len() <= 100,
        forall |i: int| 0 <= i < order.len() ==> 1 <= #[trigger] order[i] <= order.len() as i32,
        forall |i: int, j: int| 0 <= i < j < order.len() ==> order[i] != order[j],
        forall |id: int| 1 <= id <= order.len() ==> #[trigger] order@.contains(id as i32),
        1 <= friends.len() <= 8,
        friends.len() <= order.len(),
        forall |i: int| 0 <= i < friends.len() ==> 1 <= #[trigger] friends[i] <= order.len() as i32,
        forall |i: int, j: int| 0 <= i < j < friends.len() ==> friends[i] < friends[j],
        forall |i: int| 0 <= i < friends.len() ==> order@.contains(#[trigger] friends[i]),
    ensures
        1 <= result.0.len() <= 100,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= result.0.len() as i32,
        forall |i: int, j: int| 0 <= i < j < result.0.len() ==> result.0[i] != result.0[j],
        forall |id: int| 1 <= id <= result.0.len() ==> #[trigger] result.0@.contains(id as i32),
        1 <= result.1.len() <= 8,
        result.1.len() <= result.0.len(),
        forall |i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= result.0.len() as i32,
        forall |i: int, j: int| 0 <= i < j < result.1.len() ==> result.1[i] < result.1[j],
        forall |i: int| 0 <= i < result.1.len() ==> result.0@.contains(#[trigger] result.1[i]),
{
    if mutation_kind == 1 && friends.len() > 1 {
        // Drop last friend
        let mut f = friends;
        f.pop();
        proof {
            assert(f.len() >= 1);
            assert forall |k: int| 0 <= k < f.len() implies 1 <= #[trigger] f[k] <= order.len() as i32 by {};
            assert forall |k: int, l: int| 0 <= k < l < f.len() implies f[k] < f[l] by {};
            assert forall |k: int| 0 <= k < f.len() implies order@.contains(#[trigger] f[k]) by {};
        }
        (order, f)
    } else if mutation_kind == 2 && friends.len() > 1 {
        // Drop first friend: copy friends[1..]
        let mut f: Vec<i32> = Vec::new();
        let mut i: usize = 1;
        while i < friends.len()
            invariant
                1 <= i <= friends.len(),
                f.len() == (i - 1) as int,
                friends.len() > 1,
                friends.len() <= 8,
                friends.len() <= order.len(),
                forall |k: int| 0 <= k < f.len() ==> f[k] == friends[k + 1],
            decreases friends.len() - i,
        {
            f.push(friends[i]);
            i += 1;
        }
        proof {
            assert(f.len() >= 1);
            assert(f.len() <= 8) by {
                assert(f.len() == friends.len() - 1);
            };
            assert forall |k: int| 0 <= k < f.len() implies 1 <= #[trigger] f[k] <= order.len() as i32 by {
                assert(f[k] == friends[k + 1]);
            };
            assert forall |k: int, l: int| 0 <= k < l < f.len() implies f[k] < f[l] by {
                assert(f[k] == friends[k + 1]);
                assert(f[l] == friends[l + 1]);
            };
            assert forall |k: int| 0 <= k < f.len() implies order@.contains(#[trigger] f[k]) by {
                assert(f[k] == friends[k + 1]);
            };
        }
        (order, f)
    } else if mutation_kind == 3 {
        // Keep only first friend
        let mut f: Vec<i32> = Vec::new();
        f.push(friends[0]);
        proof {
            assert(f[0int] == friends[0int]);
            assert(f.len() == 1);
        }
        (order, f)
    } else if mutation_kind == 4 {
        // Keep only last friend
        let last = friends.len() - 1;
        let mut f: Vec<i32> = Vec::new();
        f.push(friends[last]);
        proof {
            assert(f[0int] == friends[last as int]);
            assert(f.len() == 1);
        }
        (order, f)
    } else if mutation_kind == 5 {
        // Keep only middle friend
        let mid = friends.len() / 2;
        let mut f: Vec<i32> = Vec::new();
        f.push(friends[mid]);
        proof {
            assert(f[0int] == friends[mid as int]);
            assert(f.len() == 1);
        }
        (order, f)
    } else {
        // Identity (mutation_kind == 0 or fallback)
        (order, friends)
    }
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

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

fn random_permutation(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut perm: Vec<i32> = (1..=n as i32).collect();
    // Fisher-Yates shuffle
    for i in (1..n).rev() {
        let j = rng.gen_range_usize(0, i);
        perm.swap(i, j);
    }
    perm
}

fn random_friends(rng: &mut Rng, n: usize, count: usize) -> Vec<i32> {
    // Select `count` distinct values from 1..=n, return sorted
    let mut pool: Vec<i32> = (1..=n as i32).collect();
    // Partial Fisher-Yates to pick `count` elements
    let c = count.min(n);
    for i in 0..c {
        let j = rng.gen_range_usize(i, n - 1);
        pool.swap(i, j);
    }
    let mut friends: Vec<i32> = pool[..c].to_vec();
    friends.sort();
    friends
}

extern crate serde_json;
use serde_json::json;

struct Solution;
include!("../code.rs");

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3668);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    macro_rules! emit {
        ($order:expr, $friends:expr, $mk:expr) => {
            if count < goal {
                let order_val: Vec<i32> = $order;
                let friends_val: Vec<i32> = $friends;
                let mk_val: u8 = $mk;
                let (ord_out, fr_out) = generate_test_case(order_val, friends_val, mk_val);
                let result = Solution::recover_order(ord_out.clone(), fr_out.clone());
                let line = json!({
                    "input": {"order": ord_out, "friends": fr_out},
                    "output": result
                }).to_string();
                if seen.insert(line.clone()) {
                    writeln!(out, "{}", line).unwrap();
                    count += 1;
                }
            }
        };
    }

    // ---- LeetCode examples ----
    emit!(vec![3, 1, 2, 5, 4], vec![1, 3, 4], 0);
    emit!(vec![1, 4, 5, 3, 2], vec![2, 5], 0);

    // ---- Examples with all mutations ----
    for mk in 0u8..=5 {
        emit!(vec![3, 1, 2, 5, 4], vec![1, 3, 4], mk);
        emit!(vec![1, 4, 5, 3, 2], vec![2, 5], mk);
    }

    // ---- Single element order ----
    emit!(vec![1], vec![1], 0);
    for mk in [0u8, 3, 4, 5] {
        emit!(vec![1], vec![1], mk);
    }

    // ---- Two elements, all mutations ----
    for mk in 0u8..=5 {
        emit!(vec![1, 2], vec![1, 2], mk);
        emit!(vec![2, 1], vec![1, 2], mk);
        emit!(vec![2, 1], vec![1], mk);
        emit!(vec![1, 2], vec![2], mk);
    }

    // ---- Identity permutation, varied friend counts ----
    for n in [3usize, 5, 8, 10, 20, 50, 100] {
        let order: Vec<i32> = (1..=n as i32).collect();
        for nf in [1usize, 2, 4, 8.min(n)] {
            if nf <= n && nf >= 1 {
                let friends: Vec<i32> = (1..=nf as i32).collect();
                for mk in 0u8..=5 {
                    emit!(order.clone(), friends.clone(), mk);
                }
            }
        }
    }

    // ---- Reversed permutation, friends at end ----
    for n in [5usize, 10, 50, 100] {
        let order: Vec<i32> = (1..=n as i32).rev().collect();
        let nf = 8.min(n);
        let friends: Vec<i32> = ((n as i32 - nf as i32 + 1)..=n as i32).collect();
        for mk in 0u8..=5 {
            emit!(order.clone(), friends.clone(), mk);
        }
    }

    // ---- Random small (n=2..10), all mutations ----
    for _ in 0..5 {
        let n = rng.gen_range_usize(2, 10);
        let order = random_permutation(&mut rng, n);
        let nf = rng.gen_range_usize(1, 8.min(n));
        let friends = random_friends(&mut rng, n, nf);
        for mk in 0u8..=5 {
            emit!(order.clone(), friends.clone(), mk);
        }
    }

    // ---- Random medium (n=11..50), random mutations ----
    for _ in 0..10 {
        let n = rng.gen_range_usize(11, 50);
        let order = random_permutation(&mut rng, n);
        let nf = rng.gen_range_usize(1, 8.min(n));
        let friends = random_friends(&mut rng, n, nf);
        let mk = rng.gen_range_usize(0, 5) as u8;
        emit!(order.clone(), friends.clone(), mk);
        emit!(order.clone(), friends.clone(), 0);
    }

    // ---- Random large (n=51..100), random mutations ----
    for _ in 0..10 {
        let n = rng.gen_range_usize(51, 100);
        let order = random_permutation(&mut rng, n);
        let nf = rng.gen_range_usize(1, 8);
        let friends = random_friends(&mut rng, n, nf);
        let mk = rng.gen_range_usize(0, 5) as u8;
        emit!(order.clone(), friends.clone(), mk);
    }

    // ---- Max size n=100, max friends=8 ----
    for _ in 0..3 {
        let order = random_permutation(&mut rng, 100);
        let friends = random_friends(&mut rng, 100, 8);
        for mk in 0u8..=5 {
            emit!(order.clone(), friends.clone(), mk);
        }
    }

    // ---- Single friend from various positions ----
    for _ in 0..5 {
        let n = rng.gen_range_usize(5, 50);
        let order = random_permutation(&mut rng, n);
        let fv = rng.gen_range_usize(1, n) as i32;
        emit!(order.clone(), vec![fv], 0);
    }

    // ---- Fill remaining with random ----
    while count < goal {
        let n = rng.gen_range_usize(1, 100);
        let order = random_permutation(&mut rng, n);
        let nf = rng.gen_range_usize(1, 8.min(n));
        let friends = random_friends(&mut rng, n, nf);
        let mk = rng.gen_range_usize(0, 5) as u8;
        emit!(order, friends, mk);
    }
}
