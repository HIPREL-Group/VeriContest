use vstd::prelude::*;

verus! {

pub open spec fn is_prime_spec(n: int) -> bool {
    n >= 2 && forall|d: int| 2 <= d < n ==> #[trigger](n % d) != 0
}

pub open spec fn fraction_less_spec(s: Seq<i32>, a: int, b: int, num_idx: int, den_idx: int) -> bool {
    (s[a] as int) * (s[den_idx] as int) < (s[num_idx] as int) * (s[b] as int)
}

pub open spec fn count_less_inner_spec(s: Seq<i32>, num_idx: int, den_idx: int, a: int, b: int) -> nat
    decreases (s.len() - b) as nat
{
    if b >= s.len() {
        0nat
    } else if a >= b {
        0nat
    } else {
        let add = if fraction_less_spec(s, a, b, num_idx, den_idx) { 1nat } else { 0nat };
        add + count_less_inner_spec(s, num_idx, den_idx, a, b + 1)
    }
}

pub open spec fn count_less_outer_spec(s: Seq<i32>, num_idx: int, den_idx: int, a: int) -> nat
    decreases (s.len() - a) as nat
{
    if a >= s.len() {
        0nat
    } else {
        count_less_inner_spec(s, num_idx, den_idx, a, a + 1)
            + count_less_outer_spec(s, num_idx, den_idx, a + 1)
    }
}

pub open spec fn count_fractions_less_spec(s: Seq<i32>, num_idx: int, den_idx: int) -> nat {
    count_less_outer_spec(s, num_idx, den_idx, 0)
}

// Build the standard prefix-prime array: [1, 2, 3, 5, 7, 11, 13, 17, 19, 23, ...]
// We provide the primes as input and verify via a precondition.

pub fn generate_test_case(
    primes: &Vec<i32>,
    n: usize,
    k: i32,
    i_wit: usize,
    j_wit: usize,
) -> (result: (Vec<i32>, i32))
    requires
        2 <= n <= 1000,
        n <= primes.len() + 1,
        forall|i: int| 0 <= i < primes.len() ==> 2 <= #[trigger] primes[i] <= 30_000,
        forall|i: int| 0 <= i < primes.len() ==> is_prime_spec(primes[i] as int),
        forall|i: int, j: int| 0 <= i < j < primes.len() ==> primes[i] < primes[j],
        // The assembled array will be [1] ++ primes[0..n-1]
        1 <= k,
        k <= (n * (n - 1) / 2) as i32,
        // Witness indices
        0 <= i_wit < j_wit < n,
        // Witness condition: the count_fractions_less at these indices equals k-1
        ({
            let s = seq![1i32] + primes@.subrange(0, (n - 1) as int);
            count_fractions_less_spec(s, i_wit as int, j_wit as int) == (k - 1) as nat
        }),
    ensures
        ({
            let arr = result.0;
            let kk = result.1;
            &&& 2 <= arr.len() <= 1000
            &&& arr.len() == n
            &&& kk == k
            &&& forall|i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 30_000
            &&& arr[0] == 1
            &&& forall|i: int| 1 <= i < arr.len() ==> is_prime_spec(arr[i] as int)
            &&& forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] < arr[j]
            &&& 1 <= kk <= (arr.len() * (arr.len() - 1) / 2) as int
            &&& exists|i: int, j: int|
                0 <= i < j < arr.len()
                && #[trigger] count_fractions_less_spec(arr@, i, j) == (kk - 1) as nat
        }),
{
    let mut arr: Vec<i32> = Vec::new();
    arr.push(1i32);

    let mut idx: usize = 0;
    while idx < n - 1
        invariant
            2 <= n <= 1000,
            n <= primes.len() + 1,
            0 <= idx <= n - 1,
            arr.len() == idx + 1,
            arr[0] == 1i32,
            forall|i: int| 0 <= i < primes.len() ==> 2 <= #[trigger] primes[i] <= 30_000,
            forall|i: int| 0 <= i < primes.len() ==> is_prime_spec(primes[i] as int),
            forall|i: int, j: int| 0 <= i < j < primes.len() ==> primes[i] < primes[j],
            forall|i: int| 1 <= i < arr.len() ==> #[trigger] arr[i] == primes[i - 1],
        decreases n - 1 - idx,
    {
        arr.push(primes[idx]);
        idx = idx + 1;
    }

    proof {
        let s = seq![1i32] + primes@.subrange(0, (n - 1) as int);
        assert(arr.len() == n);
        assert(arr@.len() == n);
        assert(s.len() == n);
        assert forall|i: int| 0 <= i < arr@.len() implies arr@[i] == s[i] by {
            if i == 0 {
                assert(arr@[0] == 1i32);
                assert(s[0] == 1i32);
            } else {
                assert(arr@[i] == primes[i - 1]);
                assert(s[i] == primes@.subrange(0, (n - 1) as int)[i - 1]);
                assert(s[i] == primes[i - 1]);
            }
        }
        assert(arr@ =~= s);

        assert forall|i: int| 0 <= i < arr@.len() implies 1 <= #[trigger] arr@[i] <= 30_000 by {
            if i == 0 {
            } else {
                assert(arr@[i] == primes[i - 1]);
            }
        }

        assert forall|i: int| 1 <= i < arr@.len() implies is_prime_spec(arr@[i] as int) by {
            assert(arr@[i] == primes[i - 1]);
        }

        assert forall|i: int, j: int| 0 <= i < j < arr@.len() implies arr@[i] < arr@[j] by {
            if i == 0 {
                assert(arr@[0] == 1);
                assert(arr@[j] == primes[j - 1]);
                assert(primes[j - 1] >= 2);
            } else {
                assert(arr@[i] == primes[i - 1]);
                assert(arr@[j] == primes[j - 1]);
                assert(primes[i - 1] < primes[j - 1]);
            }
        }

        assert(count_fractions_less_spec(arr@, i_wit as int, j_wit as int) == (k - 1) as nat);
    }

    (arr, k)
}

} // verus!

// ===== Unverified part =====

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(1) }
    }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
}

// Generate the first N primes via trial division. N=999 to ensure we have enough.
fn generate_primes(count: usize) -> Vec<i32> {
    let mut primes: Vec<i32> = Vec::new();
    let mut n: i32 = 2;
    while primes.len() < count && n <= 30_000 {
        let mut is_p = true;
        let mut d = 2i32;
        while d * d <= n {
            if n % d == 0 {
                is_p = false;
                break;
            }
            d += 1;
        }
        if is_p {
            primes.push(n);
        }
        n += 1;
    }
    primes
}

// Count fractions arr[a]/arr[b] < arr[num_idx]/arr[den_idx]
fn count_fractions_less(arr: &[i32], num_idx: usize, den_idx: usize) -> u64 {
    let mut count: u64 = 0;
    let n = arr.len();
    for a in 0..n {
        for b in (a + 1)..n {
            let lhs = arr[a] as i64 * arr[den_idx] as i64;
            let rhs = arr[num_idx] as i64 * arr[b] as i64;
            if lhs < rhs {
                count += 1;
            }
        }
    }
    count
}

// For a given arr, find (i,j) such that count_fractions_less == k-1 by sorting all fractions.
// Returns (i, j, k) where k is between 1 and total pairs.
fn find_witness(arr: &[i32], k_target: u64) -> Option<(usize, usize)> {
    let n = arr.len();
    let mut pairs: Vec<(i64, i64, usize, usize)> = Vec::new();
    for i in 0..n {
        for j in (i + 1)..n {
            pairs.push((arr[i] as i64, arr[j] as i64, i, j));
        }
    }
    // Sort by fraction value a/b, i.e. a1*b2 < a2*b1
    pairs.sort_by(|x, y| {
        let lhs = x.0 * y.1;
        let rhs = y.0 * x.1;
        lhs.cmp(&rhs)
    });
    if k_target == 0 || (k_target as usize) > pairs.len() {
        return None;
    }
    let chosen = pairs[(k_target - 1) as usize];
    let (i, j) = (chosen.2, chosen.3);
    // Verify
    let cnt = count_fractions_less(arr, i, j);
    if cnt == k_target - 1 {
        Some((i, j))
    } else {
        // tied fractions: find one with matching count
        for &(_, _, ii, jj) in &pairs {
            if count_fractions_less(arr, ii, jj) == k_target - 1 {
                return Some((ii, jj));
            }
        }
        None
    }
}

fn print_json(arr: &[i32], k: i32) {
    print!("{{\"arr\":[");
    for i in 0..arr.len() {
        if i > 0 { print!(","); }
        print!("{}", arr[i]);
    }
    println!("],\"k\":{}}}", k);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);

    let all_primes = generate_primes(999);

    let total = 200usize;
    for t in 0..total {
        let mode = t % 10;
        let n: usize = match mode {
            0 => 2,
            1 => 3,
            2 => 4,
            3 => rng.gen_range_usize(5, 20),
            4 => rng.gen_range_usize(20, 100),
            5 => rng.gen_range_usize(100, 500),
            6 => 1000,
            7 => rng.gen_range_usize(2, 10),
            8 => rng.gen_range_usize(50, 200),
            _ => rng.gen_range_usize(2, 1000),
        };
        let n = n.min(all_primes.len() + 1).max(2);

        // Build arr = [1] ++ primes[0..n-1]
        let mut arr: Vec<i32> = Vec::new();
        arr.push(1);
        for i in 0..(n - 1) {
            arr.push(all_primes[i]);
        }

        let total_pairs = (n * (n - 1) / 2) as u64;
        let k: u64 = match mode {
            0 => 1,
            1 => total_pairs,
            2 => (total_pairs + 1) / 2,
            _ => {
                if total_pairs == 0 { 1 } else { rng.gen_range_usize(1, total_pairs as usize) as u64 }
            }
        };
        let k = k.max(1).min(total_pairs);

        let (i_wit, j_wit) = match find_witness(&arr, k) {
            Some(p) => p,
            None => continue,
        };

        // Build primes vec to pass (first n-1 primes)
        let primes_in: Vec<i32> = all_primes[..(n - 1)].to_vec();

        let (result_arr, result_k) = generate_test_case(&primes_in, n, k as i32, i_wit, j_wit);
        print_json(&result_arr, result_k);
    }
}