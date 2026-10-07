use vstd::prelude::*;

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn seq_sum(s: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::seq_sum(s, end - 1) + s[end - 1] as int
        }
    }

    pub open spec fn appears_in(s: Seq<i32>, value: i32) -> bool {
        exists |i: int| 0 <= i < s.len() && #[trigger] s[i] == value
    }

    pub open spec fn valid_swap_int(
        alice_sizes: Seq<i32>,
        bob_sizes: Seq<i32>,
        alice_box: int,
        bob_box: int,
    ) -> bool {
        &&& 1 <= alice_box <= 100_000
        &&& 1 <= bob_box <= 100_000
        &&& Self::appears_in(alice_sizes, alice_box as i32)
        &&& Self::appears_in(bob_sizes, bob_box as i32)
        &&& Self::seq_sum(alice_sizes, alice_sizes.len() as int) - alice_box + bob_box
            == Self::seq_sum(bob_sizes, bob_sizes.len() as int) - bob_box + alice_box
    }

    /// seq_sum over a prefix of s.push(v) equals seq_sum over the same prefix of s.
    proof fn lemma_seq_sum_prefix_push(s: Seq<i32>, v: i32, n: int)
        requires
            0 <= n <= s.len(),
        ensures
            Self::seq_sum(s.push(v), n) == Self::seq_sum(s, n),
        decreases n,
    {
        if n > 0 {
            Self::lemma_seq_sum_prefix_push(s, v, n - 1);
            assert(s.push(v)[n - 1] == s[n - 1]);
        }
    }

    /// seq_sum of s.push(v) over the full new length equals seq_sum(s, s.len()) + v.
    proof fn lemma_seq_sum_push(s: Seq<i32>, v: i32)
        ensures
            Self::seq_sum(s.push(v), (s.len() + 1) as int)
                == Self::seq_sum(s, s.len() as int) + v as int,
    {
        Self::lemma_seq_sum_prefix_push(s, v, s.len() as int);
        assert(s.push(v)[s.len() as int] == v);
    }

    /// Build (alice_sizes, bob_sizes) from swap-pair values and shared fillers.
    ///
    /// alice = [a_val, a_val - b_val] ++ shared
    /// bob   = [b_val]               ++ shared
    ///
    /// The swap pair (a_val, b_val) is valid because shared fillers contribute
    /// equally to both sums.
    pub fn generate_test_case(
        a_val: i32,
        b_val: i32,
        shared: &Vec<i32>,
        mutation_kind: u8,
    ) -> (result: (Vec<i32>, Vec<i32>))
        requires
            2 <= a_val <= 100_000i32,
            1 <= b_val <= 100_000i32,
            b_val < a_val,
            a_val as int - b_val as int <= 100_000,
            shared.len() <= 9_998,
            forall|i: int| 0 <= i < shared.len() ==> 1 <= #[trigger] shared[i] <= 100_000i32,
        ensures
            1 <= result.0.len() <= 10_000,
            1 <= result.1.len() <= 10_000,
            forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100_000,
            forall|j: int| 0 <= j < result.1.len() ==> 1 <= #[trigger] result.1[j] <= 100_000,
            Self::seq_sum(result.0@, result.0.len() as int)
                != Self::seq_sum(result.1@, result.1.len() as int),
            exists|alice_box: int, bob_box: int|
                Self::valid_swap_int(result.0@, result.1@, alice_box, bob_box),
    {
        let extra: i32 = (a_val - b_val) as i32;

        let mut alice: Vec<i32> = Vec::new();
        let mut bob: Vec<i32> = Vec::new();

        if mutation_kind == 1 {
            alice.push(extra);
            alice.push(a_val);
        } else {
            alice.push(a_val);
            alice.push(extra);
        }
        bob.push(b_val);

        proof {
            Self::lemma_seq_sum_push(Seq::<i32>::empty(), alice[0]);
            Self::lemma_seq_sum_push(Seq::<i32>::empty().push(alice[0]), alice[1]);
            Self::lemma_seq_sum_push(Seq::<i32>::empty(), b_val);
        }

        let ghost mut alice_sum: int = a_val as int + extra as int;
        let ghost mut bob_sum: int = b_val as int;

        assert(Self::seq_sum(alice@, alice.len() as int) == alice_sum);
        assert(Self::seq_sum(bob@, bob.len() as int) == bob_sum);

        let mut i: usize = 0;
        while i < shared.len()
            invariant
                0 <= i <= shared.len(),
                alice.len() == 2 + i,
                bob.len() == 1 + i,
                shared.len() <= 9_998,
                forall|k: int| 0 <= k < shared.len() ==> 1 <= #[trigger] shared[k] <= 100_000i32,
                forall|k: int| 0 <= k < alice.len() ==> 1 <= #[trigger] alice[k] <= 100_000,
                forall|k: int| 0 <= k < bob.len() ==> 1 <= #[trigger] bob[k] <= 100_000,
                alice_sum == a_val as int + extra as int
                    + Self::seq_sum(shared@, i as int) - Self::seq_sum(shared@, 0),
                bob_sum == b_val as int
                    + Self::seq_sum(shared@, i as int) - Self::seq_sum(shared@, 0),
                Self::seq_sum(alice@, alice.len() as int) == alice_sum,
                Self::seq_sum(bob@, bob.len() as int) == bob_sum,
                if mutation_kind == 1u8 {
                    alice[1] == a_val
                } else {
                    alice[0] == a_val
                },
                bob[0] == b_val,
            decreases shared.len() - i,
        {
            let v = shared[i];

            proof {
                Self::lemma_seq_sum_push(alice@, v);
                Self::lemma_seq_sum_push(bob@, v);
                // Show seq_sum(shared@, i+1) == seq_sum(shared@, i) + shared[i]
                Self::lemma_seq_sum_prefix_push(shared@.subrange(0, i as int), v, i as int);
                assert(Self::seq_sum(shared@, (i + 1) as int)
                    == Self::seq_sum(shared@, i as int) + shared[i as int] as int);
            }

            alice.push(v);
            bob.push(v);

            proof {
                alice_sum = alice_sum + v as int;
                bob_sum = bob_sum + v as int;
            }

            i = i + 1;
        }

        proof {
            // Prove sums differ
            assert(alice_sum - bob_sum == a_val as int + extra as int - b_val as int);
            assert(extra as int == a_val as int - b_val as int);
            assert(alice_sum - bob_sum == 2 * (a_val as int - b_val as int));
            assert(a_val > b_val);
            assert(alice_sum != bob_sum);

            // Prove valid swap exists with witness (a_val, b_val)
            if mutation_kind == 1u8 {
                assert(alice@[1int] == a_val);
            } else {
                assert(alice@[0int] == a_val);
            }
            assert(bob@[0int] == b_val);

            // Sum equation: sum_a - a_val + b_val == sum_b - b_val + a_val
            assert(alice_sum - a_val as int + b_val as int
                == bob_sum - b_val as int + a_val as int);

            assert(Self::valid_swap_int(alice@, bob@, a_val as int, b_val as int));
        }

        (alice, bob)
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

mod code_solution {
    pub struct Solution;
    include!("../code.rs");
}
use code_solution::Solution as CodeSolution;

fn random_shared(rng: &mut Rng, n: usize, lo: i32, hi: i32) -> Vec<i32> {
    let mut v = Vec::new();
    for _ in 0..n {
        v.push(rng.gen_range_i64(lo as i64, hi as i64) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(888);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    macro_rules! emit {
        ($a_val:expr, $b_val:expr, $shared:expr, $mk:expr) => {
            if count < goal {
                let a: i32 = $a_val;
                let b: i32 = $b_val;
                let sh: Vec<i32> = $shared;
                let mk: u8 = $mk;
                let (alice, bob) = Solution::generate_test_case(a, b, &sh, mk);
                let result = CodeSolution::fair_candy_swap(alice.clone(), bob.clone());
                let line = json!({
                    "input": {"aliceSizes": alice, "bobSizes": bob},
                    "output": result
                }).to_string();
                if seen.insert(line.clone()) {
                    writeln!(out, "{}", line).unwrap();
                    count += 1;
                }
            }
        };
    }

    // ---- LeetCode examples (closest constructible equivalents) ----
    emit!(2, 1, vec![], 0);
    emit!(3, 2, vec![], 0);
    emit!(3, 1, vec![1], 0);

    // ---- Boundary: minimal a_val and b_val ----
    emit!(2, 1, vec![], 0);
    emit!(2, 1, vec![], 1);

    // ---- Boundary: maximal values ----
    emit!(100_000, 99_999, vec![], 0);
    emit!(100_000, 1, vec![], 0);
    emit!(100_000, 50_000, vec![], 0);
    emit!(100_000, 1, vec![], 1);

    // ---- Small shared arrays, all mutations ----
    for mk in 0u8..=1 {
        emit!(10, 5, vec![3, 7, 1], mk);
        emit!(50, 25, vec![100, 200], mk);
        emit!(1000, 1, vec![50000], mk);
    }

    // ---- Tiny arrays with boundary shared values ----
    emit!(5, 1, vec![1], 0);
    emit!(5, 1, vec![100_000], 0);
    emit!(5, 1, vec![1, 100_000], 0);
    emit!(5, 1, vec![1, 1, 1, 1, 1], 0);

    // ---- Various a_val - b_val gaps ----
    for gap in [1i32, 2, 10, 100, 1000, 10000, 50000, 99999] {
        let a = (gap + 1).min(100_000);
        let b = 1i32;
        if a > b && (a as i64 - b as i64) <= 100_000 {
            emit!(a, b, vec![], 0);
        }
    }

    // ---- Random tiny arrays (0-5 shared elements), small values ----
    for _ in 0..8 {
        let n_shared = rng.gen_range_usize(0, 5);
        let shared = random_shared(&mut rng, n_shared, 1, 1000);
        let a = rng.gen_range_i64(2, 1000) as i32;
        let b = rng.gen_range_i64(1, (a - 1) as i64) as i32;
        let mk = (rng.gen_range_i64(0, 1) as u8) % 2;
        emit!(a, b, shared, mk);
    }

    // ---- Random small arrays (5-20 shared), medium values ----
    for _ in 0..10 {
        let n_shared = rng.gen_range_usize(5, 20);
        let shared = random_shared(&mut rng, n_shared, 1, 10_000);
        let a = rng.gen_range_i64(2, 10_000) as i32;
        let b = rng.gen_range_i64(1, (a - 1) as i64) as i32;
        let mk = (rng.gen_range_i64(0, 1) as u8) % 2;
        emit!(a, b, shared, mk);
    }

    // ---- Random medium arrays (20-200 shared), full value range ----
    for _ in 0..10 {
        let n_shared = rng.gen_range_usize(20, 200);
        let shared = random_shared(&mut rng, n_shared, 1, 100_000);
        let a = rng.gen_range_i64(2, 100_000) as i32;
        let b = rng.gen_range_i64(1, (a - 1) as i64) as i32;
        if (a as i64 - b as i64) <= 100_000 {
            let mk = (rng.gen_range_i64(0, 1) as u8) % 2;
            emit!(a, b, shared, mk);
        }
    }

    // ---- Random large arrays (500-5000 shared) ----
    for _ in 0..6 {
        let n_shared = rng.gen_range_usize(500, 5000);
        let shared = random_shared(&mut rng, n_shared, 1, 100_000);
        let a = rng.gen_range_i64(2, 100_000) as i32;
        let b = rng.gen_range_i64(1, (a - 1) as i64) as i32;
        if (a as i64 - b as i64) <= 100_000 {
            let mk = (rng.gen_range_i64(0, 1) as u8) % 2;
            emit!(a, b, shared, mk);
        }
    }

    // ---- Maximum size (9998 shared, total alice=10000, bob=9999) ----
    {
        let shared = random_shared(&mut rng, 9998, 1, 100);
        emit!(100, 50, shared, 0);
    }

    // ---- Near-max shared with uniform values ----
    {
        let shared = vec![1i32; 9998];
        emit!(2, 1, shared.clone(), 0);
        emit!(100_000, 99_999, shared, 1);
    }

    // ---- All-same shared values ----
    for v in [1i32, 50_000, 100_000] {
        let shared = vec![v; 10];
        emit!(100, 50, shared, 0);
    }

    // ---- Fill remaining with diverse random inputs ----
    while count < goal {
        let n_shared = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(0, 5),
            1 => rng.gen_range_usize(5, 50),
            2 => rng.gen_range_usize(50, 500),
            3 => rng.gen_range_usize(500, 5000),
            _ => rng.gen_range_usize(0, 9998),
        };
        let n_shared = n_shared.min(9998);
        let val_hi = match rng.gen_range_usize(0, 2) {
            0 => 1000,
            1 => 10_000,
            _ => 100_000,
        };
        let shared = random_shared(&mut rng, n_shared, 1, val_hi);
        let a = rng.gen_range_i64(2, 100_000) as i32;
        let b = rng.gen_range_i64(1, (a - 1) as i64) as i32;
        if (a as i64 - b as i64) <= 100_000 {
            let mk = (rng.gen_range_i64(0, 1) as u8) % 2;
            emit!(a, b, shared, mk);
        }
    }
}
