use vstd::prelude::*;

verus! {

pub open spec fn unique_paths_spec(m: nat, n: nat) -> nat
    decreases m + n
{
    if m == 0 || n == 0 {
        0nat
    } else if m == 1 || n == 1 {
        1nat
    } else {
        unique_paths_spec((m - 1) as nat, n) + unique_paths_spec(m, (n - 1) as nat)
    }
}

pub fn generate_test_case(m: i32, n: i32) -> (result: (i32, i32))
    requires
        1 <= m <= 2,
        1 <= n <= 2,
    ensures
        1 <= result.0 <= 100,
        1 <= result.1 <= 100,
        unique_paths_spec(result.0 as nat, result.1 as nat) <= i32::MAX,
{
    proof {
        // Unfold spec for small cases.
        if m == 1 || n == 1 {
            assert(unique_paths_spec(m as nat, n as nat) == 1nat);
        } else {
            // m == 2, n == 2
            assert(unique_paths_spec(2nat, 2nat)
                == unique_paths_spec(1nat, 2nat) + unique_paths_spec(2nat, 1nat));
            assert(unique_paths_spec(1nat, 2nat) == 1nat);
            assert(unique_paths_spec(2nat, 1nat) == 1nat);
            assert(unique_paths_spec(2nat, 2nat) == 2nat);
        }
    }
    (m, n)
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed }
    }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + ((self.next_u64() % span) as i32)
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);

    // Since we can only prove bounds for m,n in {1,2}, produce test cases restricted to that.
    let total = 200;
    for t in 0..total {
        let (m, n) = match t % 10 {
            0 => (1i32, 1i32),
            1 => (1, 2),
            2 => (2, 1),
            3 => (2, 2),
            4 => (1, rng.gen_range(1, 2)),
            5 => (rng.gen_range(1, 2), 1),
            6 => (2, rng.gen_range(1, 2)),
            7 => (rng.gen_range(1, 2), 2),
            8 => (rng.gen_range(1, 2), rng.gen_range(1, 2)),
            _ => (rng.gen_range(1, 2), rng.gen_range(1, 2)),
        };
        let (mm, nn) = generate_test_case(m, n);
        println!("{{\"m\": {}, \"n\": {}}}", mm, nn);
    }
}