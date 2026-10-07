use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, k: i32, vals: Vec<i32>, mutation_kind: u8) -> (result: (Vec<i32>, i32))
    requires
        1 <= n <= 500,
        vals.len() == n,
        1 <= k <= 500,
        forall|i: int| 0 <= i < n as int ==> 0 <= (#[trigger] vals[i] as int) && vals[i] <= 500,
    ensures
        1 <= result.0.len() && result.0.len() <= 500,
        1 <= result.1 <= 500,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] && result.0[i] <= 500,
{
    if mutation_kind == 0 {
        // identity
        (vals, k)
    } else if mutation_kind == 1 {
        // set all elements to 0
        let mut y = vals;
        let mut i: usize = 0;
        while i < n
            invariant
                1 <= n <= 500,
                y.len() == n,
                0 <= i <= n,
                forall|j: int| 0 <= j < i ==> (#[trigger] y[j] == 0i32),
                forall|j: int| i as int <= j < n as int ==> 0 <= (#[trigger] y[j] as int) && y[j] <= 500,
            decreases n - i,
        {
            y.set(i, 0i32);
            i += 1;
        }
        assert forall|j: int| 0 <= j < y.len() implies 0 <= (#[trigger] y[j] as int) && y[j] <= 500 by {}
        (y, k)
    } else if mutation_kind == 2 {
        // set all elements to 500
        let mut y = vals;
        let mut i: usize = 0;
        while i < n
            invariant
                1 <= n <= 500,
                y.len() == n,
                0 <= i <= n,
                forall|j: int| 0 <= j < i ==> (#[trigger] y[j] == 500i32),
                forall|j: int| i as int <= j < n as int ==> 0 <= (#[trigger] y[j] as int) && y[j] <= 500,
            decreases n - i,
        {
            y.set(i, 500i32);
            i += 1;
        }
        assert forall|j: int| 0 <= j < y.len() implies 0 <= (#[trigger] y[j] as int) && y[j] <= 500 by {}
        (y, k)
    } else if mutation_kind == 3 && vals.len() >= 1 {
        // set first element to 0
        let mut y = vals;
        y.set(0, 0i32);
        assert forall|j: int| 0 <= j < y.len() implies 0 <= (#[trigger] y[j] as int) && y[j] <= 500 by {}
        (y, k)
    } else if mutation_kind == 4 && vals.len() >= 1 {
        // set last element to 0
        let mut y = vals;
        let last = y.len() - 1;
        y.set(last, 0i32);
        assert forall|j: int| 0 <= j < y.len() implies 0 <= (#[trigger] y[j] as int) && y[j] <= 500 by {}
        (y, k)
    } else if mutation_kind == 5 {
        // set k to 1
        (vals, 1i32)
    } else if mutation_kind == 6 {
        // set k to 500
        (vals, 500i32)
    } else if mutation_kind == 7 && vals.len() >= 1 {
        // set first element to 500
        let mut y = vals;
        y.set(0, 500i32);
        assert forall|j: int| 0 <= j < y.len() implies 0 <= (#[trigger] y[j] as int) && y[j] <= 500 by {}
        (y, k)
    } else {
        // fallback: identity
        (vals, k)
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

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        lo + (self.next_u64() as i32).abs() % (hi - lo + 1)
    }

    fn gen_u8(&mut self) -> u8 {
        (self.next_u64() % 256) as u8
    }
}

struct Solution;
include!("../code.rs");

fn random_vals(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i32(0, 500));
    }
    v
}

fn main() {
    use std::io::Write;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);

    let mut generated = 0usize;

    // Example 1: n=3, k=5, a=[2,0,1] -> total=4, b=[2,3,2]
    {
        let a: Vec<i32> = vec![2, 0, 1];
        let k = 5i32;
        let (total, b) = Solution::cormen_walk_schedule(a.clone(), k);
        writeln!(out, "{}", json!({
            "input": {"a": a, "k": k},
            "output": {"total": total, "b": b}
        })).unwrap();
        generated += 1;
    }

    // Example 2: n=3, k=1, a=[0,0,0] -> total=1, b=[0,1,0]
    {
        let a: Vec<i32> = vec![0, 0, 0];
        let k = 1i32;
        let (total, b) = Solution::cormen_walk_schedule(a.clone(), k);
        writeln!(out, "{}", json!({
            "input": {"a": a, "k": k},
            "output": {"total": total, "b": b}
        })).unwrap();
        generated += 1;
    }

    // Example 3: n=4, k=6, a=[2,4,3,5] -> total=0, b=[2,4,3,5]
    {
        let a: Vec<i32> = vec![2, 4, 3, 5];
        let k = 6i32;
        let (total, b) = Solution::cormen_walk_schedule(a.clone(), k);
        writeln!(out, "{}", json!({
            "input": {"a": a, "k": k},
            "output": {"total": total, "b": b}
        })).unwrap();
        generated += 1;
    }

    // Generate diverse test cases
    while generated < count {
        let n: usize = match generated % 5 {
            0 => 1,                                        // minimum
            1 => rng.gen_range_usize(1, 10),               // tiny
            2 => rng.gen_range_usize(10, 50),              // small
            3 => rng.gen_range_usize(50, 200),             // medium
            _ => rng.gen_range_usize(200, 500),            // large/max
        };

        let k: i32 = if generated % 5 == 0 {
            *[1, 500, 1, 250, 500].get(generated / 5 % 5).unwrap()
        } else {
            rng.gen_range_i32(1, 500)
        };

        let vals = random_vals(&mut rng, n);
        let mk = rng.gen_u8() % 9;
        let (a, k_out) = generate_test_case(n, k, vals, mk);

        let (total, b) = Solution::cormen_walk_schedule(a.clone(), k_out);

        writeln!(out, "{}", json!({
            "input": {"a": a, "k": k_out},
            "output": {"total": total, "b": b}
        })).unwrap();
        generated += 1;
    }
}
