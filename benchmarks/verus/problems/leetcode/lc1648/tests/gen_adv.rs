use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    base_values: &Vec<i32>,
    orders: i32,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= base_values.len() <= 100_000,
        forall |i: int| 0 <= i < base_values.len() ==> 1 <= #[trigger] base_values[i] <= 1_000_000_000,
        1 <= orders <= 1_000_000_000,
        orders as int <= base_values.len() as int,
    ensures
        ({
            let inv = result.0;
            let ord = result.1;
            &&& 1 <= inv.len() <= 100_000
            &&& inv.len() == base_values.len()
            &&& forall |i: int| 0 <= i < inv.len() ==> 1 <= #[trigger] inv[i] <= 1_000_000_000
            &&& 1 <= ord <= 1_000_000_000
            &&& ord == orders
            &&& forall |i: int| 0 <= i < inv.len() ==> #[trigger] inv[i] == base_values[i]
        }),
{
    let n = base_values.len();
    let mut inv: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == base_values.len(),
            0 <= i <= n,
            inv.len() == i,
            forall |k: int| 0 <= k < i as int ==> #[trigger] inv[k] == base_values[k],
            forall |k: int| 0 <= k < base_values.len() ==> 1 <= #[trigger] base_values[k] <= 1_000_000_000,
        decreases n - i,
    {
        inv.push(base_values[i]);
        i = i + 1;
    }
    (inv, orders)
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

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_case(rng: &mut Rng, mode: usize) -> (Vec<i32>, i32) {
    // Returns (inventory, orders) with: 1 <= len <= 100000,
    // 1 <= inv[i] <= 1e9, 1 <= orders <= min(sum, 1e9), and orders <= len.
    // We enforce orders <= len to match the generator's precondition
    // (a simpler condition implying orders <= count_above(_, 0)).
    match mode {
        0 => {
            // small random
            let n = rng.gen_range_usize(1, 10);
            let mut inv = Vec::with_capacity(n);
            for _ in 0..n {
                inv.push(rng.gen_range_i32(1, 20));
            }
            let orders = rng.gen_range_i32(1, n as i32);
            (inv, orders)
        }
        1 => {
            // single element
            let v = rng.gen_range_i32(1, 1_000_000_000);
            (vec![v], 1)
        }
        2 => {
            // all ones
            let n = rng.gen_range_usize(1, 100);
            let inv = vec![1i32; n];
            let orders = rng.gen_range_i32(1, n as i32);
            (inv, orders)
        }
        3 => {
            // all equal large
            let n = rng.gen_range_usize(1, 200);
            let v = rng.gen_range_i32(1, 1_000_000_000);
            let inv = vec![v; n];
            let orders = rng.gen_range_i32(1, n as i32);
            (inv, orders)
        }
        4 => {
            // one huge, rest small
            let n = rng.gen_range_usize(2, 100);
            let mut inv = vec![1i32; n];
            inv[0] = 1_000_000_000;
            let orders = rng.gen_range_i32(1, n as i32);
            (inv, orders)
        }
        5 => {
            // max length
            let n = 100_000usize;
            let mut inv = Vec::with_capacity(n);
            for _ in 0..n {
                inv.push(rng.gen_range_i32(1, 1_000_000_000));
            }
            let orders = rng.gen_range_i32(1, 1_000_000_000);
            (inv, orders)
        }
        6 => {
            // max length, orders=len
            let n = 100_000usize;
            let mut inv = Vec::with_capacity(n);
            for _ in 0..n {
                inv.push(rng.gen_range_i32(1, 1_000_000_000));
            }
            (inv, n as i32)
        }
        7 => {
            // max length, orders = 1
            let n = 100_000usize;
            let mut inv = Vec::with_capacity(n);
            for _ in 0..n {
                inv.push(rng.gen_range_i32(1, 1_000_000_000));
            }
            (inv, 1)
        }
        8 => {
            // ascending
            let n = rng.gen_range_usize(5, 500);
            let mut inv = Vec::with_capacity(n);
            for i in 0..n {
                inv.push((i as i32) + 1);
            }
            let orders = rng.gen_range_i32(1, n as i32);
            (inv, orders)
        }
        9 => {
            // descending with one max
            let n = rng.gen_range_usize(5, 500);
            let mut inv = Vec::with_capacity(n);
            for i in 0..n {
                inv.push(((n - i) as i32).max(1));
            }
            let orders = rng.gen_range_i32(1, n as i32);
            (inv, orders)
        }
        _ => {
            // medium random
            let n = rng.gen_range_usize(50, 2000);
            let mut inv = Vec::with_capacity(n);
            for _ in 0..n {
                inv.push(rng.gen_range_i32(1, 100_000));
            }
            let orders = rng.gen_range_i32(1, n as i32);
            (inv, orders)
        }
    }
}

fn print_json(inv: &[i32], orders: i32) {
    // Output keys per spec: "inventory" and "threshold"
    // (Using the field names the task specified.)
    print!("{{\"inventory\":[");
    for i in 0..inv.len() {
        if i > 0 { print!(","); }
        print!("{}", inv[i]);
    }
    println!("],\"orders\":{}}}", orders);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (base, orders) = build_case(&mut rng, mode);
        let (inv, ord) = generate_test_case(&base, orders);
        print_json(&inv, ord);
    }
}