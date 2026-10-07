use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, fill_val: i64) -> (b: Vec<i64>)
    requires
        2 <= n <= 200_000,
        0 <= fill_val <= 1_000_000_000,
    ensures
        b.len() == n - 1,
        forall|i: int| 0 <= i < n - 1 ==> 0 <= #[trigger] b[i] <= 1_000_000_000,
        forall|i: int| 1 <= i < n as int - 2 ==> #[trigger] b[i] <= b[i - 1] || b[i] <= b[i + 1],
{
    let len = n - 1;
    let mut b: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            len == n - 1,
            0 <= i <= len,
            b.len() == i,
            0 <= fill_val <= 1_000_000_000,
            forall|k: int| 0 <= k < i as int ==> #[trigger] b[k] == fill_val,
        decreases len - i,
    {
        b.push(fill_val);
        i = i + 1;
    }
    assert forall|i: int| 0 <= i < n - 1 implies 0 <= #[trigger] b[i] <= 1_000_000_000 by {
        assert(b[i] == fill_val);
    }
    assert forall|i: int| 1 <= i < n as int - 2 implies #[trigger] b[i] <= b[i - 1] || b[i] <= b[i + 1] by {
        assert(b[i] == fill_val);
        assert(b[i - 1] == fill_val);
    }
    b
}

} // verus!

struct Rng { state: u64 }

impl Rng {
    fn new(seed: u64) -> Self { Self { state: seed } }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i64
    }
}

fn print_case(n: usize, b: &[i64]) {
    print!("{{\"n\":{},\"b\":[", n);
    for i in 0..b.len() {
        if i > 0 { print!(","); }
        print!("{}", b[i]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let total = 200usize;

    for t in 0..total {
        let mode = t % 10;
        let (n, fill) = match mode {
            0 => (2usize, 0i64),
            1 => (2usize, 1_000_000_000i64),
            2 => (3usize, rng.gen_range_i64(0, 1_000_000_000)),
            3 => (200_000usize, 0i64),
            4 => (200_000usize, 1_000_000_000i64),
            5 => (rng.gen_range_usize(2, 100), 0i64),
            6 => (rng.gen_range_usize(2, 100), rng.gen_range_i64(0, 1_000_000_000)),
            7 => (rng.gen_range_usize(2, 1000), rng.gen_range_i64(0, 100)),
            8 => (rng.gen_range_usize(100, 10000), rng.gen_range_i64(0, 1_000_000_000)),
            _ => (rng.gen_range_usize(2, 500), rng.gen_range_i64(0, 1_000_000_000)),
        };
        let b = generate_test_case(n, fill);
        print_case(n, &b);
    }
}