use vstd::prelude::*;

verus! {

pub fn generate_test_case(player1: Vec<i32>, player2: Vec<i32>, mutation_kind: u8) -> (result: (Vec<i32>, Vec<i32>))
    requires
        player1.len() == player2.len(),
        1 <= player1.len() <= 1000,
        forall|i: int| 0 <= i < player1.len() ==> 0 <= #[trigger] player1[i] <= 10,
        forall|i: int| 0 <= i < player2.len() ==> 0 <= #[trigger] player2[i] <= 10,
    ensures
        result.0.len() == result.1.len(),
        1 <= result.0.len() <= 1000,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 10,
        forall|i: int| 0 <= i < result.1.len() ==> 0 <= #[trigger] result.1[i] <= 10,
{
    if mutation_kind == 0 {
        // identity
        (player1, player2)
    } else if mutation_kind == 1 {
        // set all player1 values to 10 (all strikes)
        let mut p1 = player1;
        let mut i: usize = 0;
        while i < p1.len()
            invariant
                0 <= i <= p1.len(),
                p1.len() == player1.len(),
                forall|j: int| 0 <= j < i ==> p1[j] == 10i32,
                forall|j: int| i <= j < p1.len() ==> p1[j] == player1[j],
            decreases p1.len() - i,
        {
            p1.set(i, 10);
            i += 1;
        }
        (p1, player2)
    } else if mutation_kind == 2 {
        // set all player2 values to 10 (all strikes)
        let mut p2 = player2;
        let mut i: usize = 0;
        while i < p2.len()
            invariant
                0 <= i <= p2.len(),
                p2.len() == player2.len(),
                forall|j: int| 0 <= j < i ==> p2[j] == 10i32,
                forall|j: int| i <= j < p2.len() ==> p2[j] == player2[j],
            decreases p2.len() - i,
        {
            p2.set(i, 10);
            i += 1;
        }
        (player1, p2)
    } else if mutation_kind == 3 {
        // set all player1 values to 0 (all gutter balls)
        let mut p1 = player1;
        let mut i: usize = 0;
        while i < p1.len()
            invariant
                0 <= i <= p1.len(),
                p1.len() == player1.len(),
                forall|j: int| 0 <= j < i ==> p1[j] == 0i32,
                forall|j: int| i <= j < p1.len() ==> p1[j] == player1[j],
            decreases p1.len() - i,
        {
            p1.set(i, 0);
            i += 1;
        }
        (p1, player2)
    } else if mutation_kind == 4 {
        // set all player2 values to 0 (all gutter balls)
        let mut p2 = player2;
        let mut i: usize = 0;
        while i < p2.len()
            invariant
                0 <= i <= p2.len(),
                p2.len() == player2.len(),
                forall|j: int| 0 <= j < i ==> p2[j] == 0i32,
                forall|j: int| i <= j < p2.len() ==> p2[j] == player2[j],
            decreases p2.len() - i,
        {
            p2.set(i, 0);
            i += 1;
        }
        (player1, p2)
    } else if mutation_kind == 5 && player1[0] < 10 {
        // nudge first player1 element up
        let mut p1 = player1;
        p1.set(0, p1[0] + 1);
        (p1, player2)
    } else if mutation_kind == 6 && player2[0] < 10 {
        // nudge first player2 element up
        let mut p2 = player2;
        p2.set(0, p2[0] + 1);
        (player1, p2)
    } else if mutation_kind == 7 && player1[0] > 0 {
        // nudge first player1 element down
        let mut p1 = player1;
        p1.set(0, p1[0] - 1);
        (p1, player2)
    } else if mutation_kind == 8 && player2[0] > 0 {
        // nudge first player2 element down
        let mut p2 = player2;
        p2.set(0, p2[0] - 1);
        (player1, p2)
    } else if mutation_kind == 9 && player1.len() >= 2 {
        // swap first two elements of player1
        let mut p1 = player1;
        let tmp = p1[0];
        p1.set(0, p1[1]);
        p1.set(1, tmp);
        (p1, player2)
    } else if mutation_kind == 10 && player2.len() >= 2 {
        // swap first two elements of player2
        let mut p2 = player2;
        let tmp = p2[0];
        p2.set(0, p2[1]);
        p2.set(1, tmp);
        (player1, p2)
    } else if mutation_kind == 11 && player1.len() < 1000 {
        // grow both arrays by pushing 0
        let mut p1 = player1;
        let mut p2 = player2;
        p1.push(0);
        p2.push(0);
        (p1, p2)
    } else if mutation_kind == 12 && player1.len() > 1 {
        // shrink both arrays by popping
        let mut p1 = player1;
        let mut p2 = player2;
        p1.pop();
        p2.pop();
        (p1, p2)
    } else if mutation_kind == 13 {
        // set first element of player1 to 10 (strike at start)
        let mut p1 = player1;
        p1.set(0, 10);
        (p1, player2)
    } else if mutation_kind == 14 {
        // set first element of player2 to 10 (strike at start)
        let mut p2 = player2;
        p2.set(0, 10);
        (player1, p2)
    } else {
        // fallback: identity
        (player1, player2)
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

fn random_player(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut scores = Vec::with_capacity(len);
    for _ in 0..len {
        scores.push(rng.gen_range_i64(0, 10) as i32);
    }
    scores
}

fn mutate(player1: Vec<i32>, player2: Vec<i32>, mutation_kind: u8) -> (Vec<i32>, Vec<i32>) {
    generate_test_case(player1, player2, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2660);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |p1: Vec<i32>, p2: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count { return; }
        let key = format!("{:?}|{:?}", p1, p2);
        if !seen.insert(key) { return; }
        let output = Solution::is_winner(p1.clone(), p2.clone());
        writeln!(out, "{}", json!({
            "input": {"player1": p1, "player2": p2},
            "output": output
        })).unwrap();
        *emitted += 1;
    };

    // Example inputs from description.md
    emit(vec![5, 10, 3, 2], vec![6, 5, 7, 3], &mut seen, &mut out, &mut emitted);
    emit(vec![3, 5, 7, 6], vec![8, 10, 10, 2], &mut seen, &mut out, &mut emitted);
    emit(vec![2, 3], vec![4, 1], &mut seen, &mut out, &mut emitted);
    emit(vec![1, 1, 1, 10, 10, 10, 10], vec![10, 10, 10, 10, 1, 1, 1], &mut seen, &mut out, &mut emitted);

    // Boundary: single element
    emit(vec![0], vec![0], &mut seen, &mut out, &mut emitted);
    emit(vec![10], vec![10], &mut seen, &mut out, &mut emitted);
    emit(vec![0], vec![10], &mut seen, &mut out, &mut emitted);
    emit(vec![10], vec![0], &mut seen, &mut out, &mut emitted);

    // All strikes vs all gutter balls
    emit(vec![10, 10, 10], vec![0, 0, 0], &mut seen, &mut out, &mut emitted);
    emit(vec![0, 0, 0], vec![10, 10, 10], &mut seen, &mut out, &mut emitted);

    // Strike followed by high scores (double scoring)
    emit(vec![10, 5, 5], vec![5, 5, 5], &mut seen, &mut out, &mut emitted);
    emit(vec![5, 5, 5], vec![10, 5, 5], &mut seen, &mut out, &mut emitted);

    // Seed pool with mutations
    let seed_cases: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![5, 10, 3, 2], vec![6, 5, 7, 3]),
        (vec![3, 5, 7, 6], vec![8, 10, 10, 2]),
        (vec![2, 3], vec![4, 1]),
        (vec![10, 10, 10], vec![0, 0, 0]),
        (vec![0], vec![0]),
        (vec![10], vec![10]),
        (vec![1, 2, 3, 4, 5], vec![5, 4, 3, 2, 1]),
        (vec![10, 0, 10, 0], vec![0, 10, 0, 10]),
    ];

    for (p1, p2) in &seed_cases {
        for mk in 0..=14u8 {
            if emitted >= count { break; }
            let (mp1, mp2) = mutate(p1.clone(), p2.clone(), mk);
            emit(mp1, mp2, &mut seen, &mut out, &mut emitted);
        }
    }

    // Random generation across size classes
    while emitted < count {
        let n: usize = match emitted % 5 {
            0 => rng.gen_range_usize(1, 3),         // tiny
            1 => rng.gen_range_usize(1, 10),         // small
            2 => rng.gen_range_usize(11, 50),        // medium
            3 => rng.gen_range_usize(51, 200),       // large
            _ => rng.gen_range_usize(201, 1000),     // max
        };

        let p1 = random_player(&mut rng, n);
        let p2 = random_player(&mut rng, n);
        let mk = (rng.next_u64() % 15) as u8;
        let (mp1, mp2) = mutate(p1, p2, mk);
        emit(mp1, mp2, &mut seen, &mut out, &mut emitted);
    }
}
