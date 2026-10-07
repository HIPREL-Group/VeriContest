use vstd::prelude::*;

verus! {

spec fn suffix_index(k: int, prefix_len: int) -> int {
    k - prefix_len - 1
}

pub fn generate_test_case(prefix: &Vec<i32>, pivot: i32, suffix: &Vec<i32>) -> (out: Vec<i32>)
    requires
        prefix.len() + suffix.len() + 1 <= 10_000,
        forall|i: int| 0 <= i < prefix.len() ==> 1 <= #[trigger] prefix[i] <= 10_000,
        1 <= pivot <= 10_000,
        forall|i: int| 0 <= i < suffix.len() ==> 1 <= #[trigger] suffix[i] <= 10_000,
    ensures
        1 <= out@.len() <= 10_000,
        forall|i: int| 0 <= i < out@.len() ==> 1 <= #[trigger] out@[i] <= 10_000,
{
    let n: usize = prefix.len() + 1 + suffix.len();
    let mut out: Vec<i32> = Vec::new();
    let mut pos: usize = 0;

    while pos < n
        invariant
            n == prefix.len() + 1 + suffix.len(),
            1 <= n <= 10_000,
            0 <= pos <= n,
            out.len() == pos,
            forall|k: int| 0 <= k < pos as int && k < (prefix.len() as int) ==> #[trigger] out@[k] == prefix[k],
            forall|k: int| 0 <= k < pos as int && k == (prefix.len() as int) ==> #[trigger] out@[k] == pivot,
            forall|k: int| 0 <= k < pos as int && (prefix.len() as int) < k ==> #[trigger] out@[k] == suffix[suffix_index(k, prefix.len() as int)],
            forall|k: int| 0 <= k < pos as int ==> 1 <= #[trigger] out@[k] <= 10_000,
            forall|i: int| 0 <= i < prefix.len() ==> 1 <= #[trigger] prefix[i] <= 10_000,
            1 <= pivot <= 10_000,
            forall|i: int| 0 <= i < suffix.len() ==> 1 <= #[trigger] suffix[i] <= 10_000,
        decreases n - pos,
    {
        if pos < prefix.len() {
            out.push(prefix[pos]);
        } else if pos == prefix.len() {
            out.push(pivot);
        } else {
            let si = pos - prefix.len() - 1;
            assert(si < suffix.len());
            assert(si as int == suffix_index(pos as int, prefix.len() as int));
            out.push(suffix[si]);
        }
        pos = pos + 1;
    }

    proof {
        assert(out@.len() == n as int);
        assert(1 <= out@.len());
        assert(out@.len() <= 10_000);
        assert forall|i: int| 0 <= i < out@.len() implies 1 <= #[trigger] out@[i] <= 10_000 by {
            if i < prefix.len() as int {
                assert(out@[i] == prefix[i]);
            } else if i == prefix.len() as int {
                assert(out@[i] == pivot);
            } else {
                assert((prefix.len() as int) < i);
                assert(out@[i] == suffix[suffix_index(i, prefix.len() as int)]);
            }
        }
    }

    out
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

fn generate_case_mode(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            let pivot = rng.gen_range_i32(1, 10_000);
            generate_test_case(&Vec::new(), pivot, &Vec::new())
        }
        1 => {
            let len = 2 + (t % 8);
            let mut prefix = Vec::new();
            for i in 0..(len - 1) {
                prefix.push((i as i32 % 10_000) + 1);
            }
            let pivot = 10_000;
            generate_test_case(&prefix, pivot, &Vec::new())
        }
        2 => {
            let len = 2 + (t % 8);
            let mut suffix = Vec::new();
            for i in 0..(len - 1) {
                suffix.push(((len - i) as i32 % 10_000) + 1);
            }
            let pivot = 1;
            generate_test_case(&Vec::new(), pivot, &suffix)
        }
        3 => {
            let n = 10_000;
            let mut prefix = Vec::new();
            for i in 0..(n - 1) {
                prefix.push(((i % 17) as i32) + 1);
            }
            let pivot = 9999;
            generate_test_case(&prefix, pivot, &Vec::new())
        }
        4 => {
            let n = 10_000;
            let mut suffix = Vec::new();
            for i in 0..(n - 1) {
                suffix.push((((i * 37) % 10_000) as i32) + 1);
            }
            let pivot = 5000;
            generate_test_case(&Vec::new(), pivot, &suffix)
        }
        5 => {
            let n = 64 + (t % 64);
            let mut prefix = Vec::new();
            let mut suffix = Vec::new();
            let lp = n / 2;
            let ls = n - lp - 1;
            for _ in 0..lp {
                prefix.push(7);
            }
            for _ in 0..ls {
                suffix.push(7);
            }
            let pivot = 7;
            generate_test_case(&prefix, pivot, &suffix)
        }
        6 => {
            let n = 50 + (t % 50);
            let mut prefix = Vec::new();
            let mut suffix = Vec::new();
            let lp = n / 3;
            let ls = n - lp - 1;
            for i in 0..lp {
                prefix.push(((i % 2) as i32) + 1);
            }
            for i in 0..ls {
                suffix.push((10000 - (i % 2) as i32).max(1));
            }
            let pivot = 5000;
            generate_test_case(&prefix, pivot, &suffix)
        }
        7 => {
            let n = 20 + (t % 40);
            let mut prefix = Vec::new();
            let mut suffix = Vec::new();
            let lp = rng.gen_range_usize(0, n - 1);
            let ls = n - lp - 1;
            for _ in 0..lp {
                prefix.push(1);
            }
            for _ in 0..ls {
                suffix.push(10_000);
            }
            let pivot = rng.gen_range_i32(1, 10_000);
            generate_test_case(&prefix, pivot, &suffix)
        }
        8 => {
            let n = 3 + (t % 97);
            let lp = n / 2;
            let ls = n - lp - 1;
            let mut prefix = Vec::new();
            let mut suffix = Vec::new();
            for i in 0..lp {
                prefix.push(((i + 1) as i32).min(10_000));
            }
            for i in 0..ls {
                suffix.push((((ls - i) + 1) as i32).min(10_000));
            }
            let pivot = 1234;
            generate_test_case(&prefix, pivot, &suffix)
        }
        9 => {
            let n = 2 + (t % 30);
            let lp = if n > 1 { rng.gen_range_usize(0, n - 1) } else { 0 };
            let ls = n - lp - 1;
            let mut prefix = Vec::new();
            let mut suffix = Vec::new();
            for _ in 0..lp {
                prefix.push(rng.gen_range_i32(1, 3));
            }
            for _ in 0..ls {
                suffix.push(rng.gen_range_i32(9998, 10_000));
            }
            let pivot = rng.gen_range_i32(1, 10_000);
            generate_test_case(&prefix, pivot, &suffix)
        }
        _ => {
            let n = rng.gen_range_usize(1, 10_000);
            let lp = if n == 1 { 0 } else { rng.gen_range_usize(0, n - 1) };
            let ls = n - lp - 1;
            let mut prefix = Vec::new();
            let mut suffix = Vec::new();
            for _ in 0..lp {
                prefix.push(rng.gen_range_i32(1, 10_000));
            }
            for _ in 0..ls {
                suffix.push(rng.gen_range_i32(1, 10_000));
            }
            let pivot = rng.gen_range_i32(1, 10_000);
            generate_test_case(&prefix, pivot, &suffix)
        }
    }
}

fn print_json(arr: &[i32]) {
    print!("{{\"arr\":[");
    for i in 0..arr.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", arr[i]);
    }
    println!("]}}");
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
    let modes = 11usize;

    for t in 0..total {
        let mode = t % modes;
        let arr = generate_case_mode(&mut rng, mode, t);
        print_json(&arr);
    }
}