use vstd::prelude::*;

verus! {

pub open spec fn customer_value_at(i: int, spike_idx: int, spike_customer: i32, filler_customer: i32) -> i32 {
    if i == spike_idx { spike_customer } else { filler_customer }
}

pub open spec fn grumpy_value_at(i: int, grumpy_start: int, grumpy_len: int) -> i32 {
    if grumpy_start <= i && i < grumpy_start + grumpy_len { 1i32 } else { 0i32 }
}

pub fn generate_test_case(
    n: usize,
    minutes: i32,
    spike_idx: usize,
    spike_customer: i32,
    filler_customer: i32,
    grumpy_start: usize,
    grumpy_len: usize,
) -> (result: (Vec<i32>, Vec<i32>, i32))
    requires
        1 <= n <= 20_000,
        1 <= minutes <= n as i32,
        spike_idx < n,
        grumpy_start + grumpy_len <= n,
        0 <= spike_customer <= 1000,
        0 <= filler_customer <= 1000,
    ensures
        result.0.len() == n,
        result.1.len() == n,
        result.2 == minutes,
        1 <= result.2 <= result.0.len(),
        result.0.len() == result.1.len(),
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 1000,
        forall|i: int| 0 <= i < result.1.len() ==> (#[trigger] result.1[i] == 0 || result.1[i] == 1),
        forall|i: int| 0 <= i < n as int ==> #[trigger] result.0[i] == customer_value_at(i, spike_idx as int, spike_customer, filler_customer),
        forall|i: int| 0 <= i < n as int ==> #[trigger] result.1[i] == grumpy_value_at(i, grumpy_start as int, grumpy_len as int),
{
    let mut customers: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n <= 20_000,
            spike_idx < n,
            0 <= spike_customer <= 1000,
            0 <= filler_customer <= 1000,
            0 <= i <= n,
            customers.len() == i,
            forall|k: int| 0 <= k < i as int ==> 0 <= #[trigger] customers[k] <= 1000,
            forall|k: int| 0 <= k < i as int ==> #[trigger] customers[k] == customer_value_at(k, spike_idx as int, spike_customer, filler_customer),
        decreases n - i,
    {
        if i == spike_idx {
            customers.push(spike_customer);
        } else {
            customers.push(filler_customer);
        }
        i = i + 1;
    }

    let mut grumpy: Vec<i32> = Vec::new();
    let mut j: usize = 0;
    while j < n
        invariant
            n <= 20_000,
            grumpy_start + grumpy_len <= n,
            0 <= j <= n,
            grumpy.len() == j,
            forall|k: int| 0 <= k < j as int ==> (#[trigger] grumpy[k] == 0 || grumpy[k] == 1),
            forall|k: int| 0 <= k < j as int ==> #[trigger] grumpy[k] == grumpy_value_at(k, grumpy_start as int, grumpy_len as int),
        decreases n - j,
    {
        if grumpy_start <= j && j < grumpy_start + grumpy_len {
            grumpy.push(1);
        } else {
            grumpy.push(0);
        }
        j = j + 1;
    }

    proof {
        assert(customers.len() == n);
        assert(grumpy.len() == n);
        assert forall|k: int| 0 <= k < customers.len() ==> 0 <= #[trigger] customers[k] <= 1000 by {
        }
        assert forall|k: int| 0 <= k < grumpy.len() ==> (#[trigger] grumpy[k] == 0 || grumpy[k] == 1) by {
        }
        assert forall|k: int| 0 <= k < n as int ==> #[trigger] customers[k] == customer_value_at(k, spike_idx as int, spike_customer, filler_customer) by {
        }
        assert forall|k: int| 0 <= k < n as int ==> #[trigger] grumpy[k] == grumpy_value_at(k, grumpy_start as int, grumpy_len as int) by {
        }
        assert(1 <= minutes);
        assert(minutes <= n as i32);
        assert(n as int == customers.len() as int);
    }

    (customers, grumpy, minutes)
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
        self.state = self
            .state
            .wrapping_mul(6364136223846793005u64)
            .wrapping_add(1442695040888963407u64);
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

fn print_json(customers: &[i32], grumpy: &[i32], minutes: i32) {
    print!("{{\"customers\":[");
    for i in 0..customers.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", customers[i]);
    }
    print!("],\"grumpy\":[");
    for i in 0..grumpy.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", grumpy[i]);
    }
    println!("],\"minutes\":{}}}", minutes);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let total = 220usize;

    for t in 0..total {
        let mode = t % 10;
        let (n, minutes, spike_idx, spike_customer, filler_customer, grumpy_start, grumpy_len) =
            match mode {
                0 => {
                    let n = 1usize;
                    let minutes = 1i32;
                    (n, minutes, 0usize, 0i32, 0i32, 0usize, 1usize)
                }
                1 => {
                    let n = 20_000usize;
                    let minutes = 1i32;
                    let spike_idx = 19_999usize;
                    (n, minutes, spike_idx, 1000i32, 0i32, spike_idx, 1usize)
                }
                2 => {
                    let n = 20_000usize;
                    let minutes = 20_000i32;
                    (n, minutes, 0usize, 1000i32, 1000i32, 0usize, n)
                }
                3 => {
                    let n = 257usize;
                    let minutes = 128i32;
                    (n, minutes, 127usize, 1000i32, 1i32, 0usize, 127usize)
                }
                4 => {
                    let n = 511usize;
                    let minutes = 255i32;
                    (n, minutes, 510usize, 999i32, 0i32, 256usize, 255usize)
                }
                5 => {
                    let n = 97usize;
                    let minutes = 1i32;
                    let idx = rng.gen_range_usize(0, n - 1);
                    (n, minutes, idx, 1000i32, 1000i32, idx, 1usize)
                }
                6 => {
                    let n = 300usize;
                    let minutes = 300i32;
                    let idx = rng.gen_range_usize(0, n - 1);
                    (n, minutes, idx, 0i32, 1000i32, 0usize, n)
                }
                7 => {
                    let n = 64usize;
                    let minutes = 7i32;
                    let gs = 58usize;
                    (n, minutes, 63usize, 1000i32, 3i32, gs, 6usize)
                }
                8 => {
                    let n = rng.gen_range_usize(1, 2000);
                    let minutes = rng.gen_range_i32(1, n as i32);
                    let spike_idx = rng.gen_range_usize(0, n - 1);
                    let spike_customer = rng.gen_range_i32(0, 1000);
                    let filler_customer = rng.gen_range_i32(0, 1000);
                    let max_len = n;
                    let grumpy_len = rng.gen_range_usize(0, max_len);
                    let grumpy_start = rng.gen_range_usize(0, n - grumpy_len);
                    (
                        n,
                        minutes,
                        spike_idx,
                        spike_customer,
                        filler_customer,
                        grumpy_start,
                        grumpy_len,
                    )
                }
                _ => {
                    let n = 10_000usize;
                    let minutes = 5000i32;
                    let spike_idx = 5000usize;
                    (n, minutes, spike_idx, 1000i32, 0i32, 2500usize, 5000usize)
                }
            };

        let (customers, grumpy, minutes_out) = generate_test_case(
            n,
            minutes,
            spike_idx,
            spike_customer,
            filler_customer,
            grumpy_start,
            grumpy_len,
        );
        print_json(&customers, &grumpy, minutes_out);
    }
}