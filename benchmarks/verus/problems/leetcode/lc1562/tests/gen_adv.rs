use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    perm: &Vec<i32>,
    m: i32,
) -> (res: (Vec<i32>, i32))
    requires
        1 <= n <= 100_000,
        perm.len() == n,
        1 <= m <= n as i32,
        forall |i: int| 0 <= i < perm.len() ==> 1 <= #[trigger] perm[i] <= n as i32,
        forall |i: int, j: int| 0 <= i < j < perm.len() ==> perm[i] != perm[j],
    ensures
        res.0.len() >= 1,
        res.0.len() <= 100_000,
        1 <= res.1 <= res.0.len() as i32,
        forall |i: int| 0 <= i < res.0.len() ==> 1 <= #[trigger] res.0[i] <= res.0.len() as i32,
        forall |i: int, j: int| 0 <= i < j < res.0.len() ==> res.0[i] != res.0[j],
{
    let mut arr: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            arr.len() == k,
            perm.len() == n,
            1 <= n <= 100_000,
            1 <= m <= n as i32,
            forall |i: int| 0 <= i < k as int ==> #[trigger] arr[i] == perm[i],
            forall |i: int| 0 <= i < perm.len() ==> 1 <= #[trigger] perm[i] <= n as i32,
            forall |i: int, j: int| 0 <= i < j < perm.len() ==> perm[i] != perm[j],
        decreases n - k,
    {
        arr.push(perm[k]);
        k += 1;
    }

    assert(arr.len() == n);
    assert(forall |i: int| 0 <= i < arr.len() ==> arr[i] == perm[i]);

    (arr, m)
}

}

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

fn make_permutation(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = (1..=n as i32).collect();
    // Fisher-Yates shuffle
    for i in (1..n).rev() {
        let j = rng.gen_range_usize(0, i);
        v.swap(i, j);
    }
    v
}

fn identity_perm(n: usize) -> Vec<i32> {
    (1..=n as i32).collect()
}

fn reverse_perm(n: usize) -> Vec<i32> {
    (1..=n as i32).rev().collect()
}

fn outward_perm(n: usize) -> Vec<i32> {
    // middle outward
    let mut res: Vec<i32> = Vec::with_capacity(n);
    let mid = (n + 1) / 2;
    let mut left = mid as i32;
    let mut right = mid as i32 + 1;
    let mut toggle = true;
    while res.len() < n {
        if toggle && left >= 1 {
            res.push(left);
            left -= 1;
            toggle = false;
        } else if right <= n as i32 {
            res.push(right);
            right += 1;
            toggle = true;
        } else if left >= 1 {
            res.push(left);
            left -= 1;
        }
    }
    res
}

fn alternating_perm(n: usize) -> Vec<i32> {
    // 1,3,5,...,2,4,6,...
    let mut res: Vec<i32> = Vec::with_capacity(n);
    let mut i = 1;
    while i <= n as i32 {
        res.push(i);
        i += 2;
    }
    let mut i = 2;
    while i <= n as i32 {
        res.push(i);
        i += 2;
    }
    res
}

fn print_json(arr: &[i32], m: i32) {
    print!("{{\"arr\":[");
    for i in 0..arr.len() {
        if i > 0 { print!(","); }
        print!("{}", arr[i]);
    }
    println!("],\"m\":{}}}", m);
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
    let modes = 10usize;

    for t in 0..total {
        let mode = t % modes;
        let n: usize = match mode {
            0 => 1,
            1 => 2 + (t % 5),
            2 => 10 + (t % 20),
            3 => 100 + (t % 50),
            4 => 1000,
            5 => 10_000,
            6 => 100_000,
            7 => 5,
            8 => 50 + (t % 10),
            _ => rng.gen_range_usize(1, 500),
        };

        let perm: Vec<i32> = match mode {
            0 => identity_perm(n),
            1 => reverse_perm(n),
            2 => outward_perm(n),
            3 => alternating_perm(n),
            4 => make_permutation(&mut rng, n),
            5 => make_permutation(&mut rng, n),
            6 => make_permutation(&mut rng, n),
            7 => identity_perm(n),
            8 => outward_perm(n),
            _ => make_permutation(&mut rng, n),
        };

        // Choose m adversarially
        let m: i32 = match mode {
            0 => 1,
            1 => n as i32,
            2 => 1,
            3 => (n as i32 + 1) / 2,
            4 => rng.gen_range_usize(1, n) as i32,
            5 => rng.gen_range_usize(1, n) as i32,
            6 => 1,
            7 => n as i32,
            8 => 2.min(n as i32),
            _ => rng.gen_range_usize(1, n) as i32,
        };
        let m = if m < 1 { 1 } else if m > n as i32 { n as i32 } else { m };

        let (arr_out, m_out) = generate_test_case(n, &perm, m);
        print_json(&arr_out, m_out);
    }
}