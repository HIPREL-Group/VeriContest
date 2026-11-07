use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    fillers: &Vec<i32>,
) -> (arr: Vec<i32>)
    requires
        2 <= fillers.len() <= 1000,
        forall |i: int| 0 <= i < fillers.len() ==>
            -1_000_000 <= #[trigger] fillers[i] <= 1_000_000,
    ensures
        2 <= arr.len() <= 1000,
        forall |i: int| 0 <= i < arr.len() ==>
            -1_000_000 <= #[trigger] arr[i] <= 1_000_000,
{
    let n = fillers.len();
    let mut arr: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == fillers.len(),
            2 <= n <= 1000,
            arr.len() == i,
            forall |k: int| 0 <= k < fillers.len() ==>
                -1_000_000 <= #[trigger] fillers[k] <= 1_000_000,
            forall |k: int| 0 <= k < arr.len() ==>
                arr[k] == fillers[k],
            forall |k: int| 0 <= k < arr.len() ==>
                -1_000_000 <= #[trigger] arr[k] <= 1_000_000,
        decreases n - i,
    {
        arr.push(fillers[i]);
        i = i + 1;
    }
    arr
}

} // verus!

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

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn clamp_i32(v: i64) -> i32 {
    if v < -1_000_000 {
        -1_000_000
    } else if v > 1_000_000 {
        1_000_000
    } else {
        v as i32
    }
}

fn build_mode(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let n = if n < 2 { 2 } else if n > 1000 { 1000 } else { n };
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // Random in range
            for _ in 0..n {
                v.push(rng.gen_range_i32(-1_000_000, 1_000_000));
            }
        }
        1 => {
            // Valid AP
            let start = rng.gen_range_i32(-500_000, 500_000);
            let diff = rng.gen_range_i32(-1000, 1000);
            // shuffle by random order
            let mut tmp: Vec<i32> = Vec::with_capacity(n);
            for i in 0..n {
                tmp.push(clamp_i32(start as i64 + diff as i64 * i as i64));
            }
            // shuffle
            for i in (1..tmp.len()).rev() {
                let j = rng.gen_range_usize(0, i);
                tmp.swap(i, j);
            }
            v = tmp;
        }
        2 => {
            // Constant sequence (valid AP with diff 0)
            let x = rng.gen_range_i32(-1_000_000, 1_000_000);
            for _ in 0..n {
                v.push(x);
            }
        }
        3 => {
            // Almost AP with one swap
            let start = rng.gen_range_i32(-500_000, 500_000);
            let diff = rng.gen_range_i32(1, 1000);
            for i in 0..n {
                v.push(clamp_i32(start as i64 + diff as i64 * i as i64));
            }
            if n >= 3 {
                let idx = rng.gen_range_usize(0, n - 1);
                v[idx] = clamp_i32(v[idx] as i64 + 1);
            }
        }
        4 => {
            // Extremes
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(-1_000_000);
                } else {
                    v.push(1_000_000);
                }
            }
        }
        5 => {
            // Duplicates
            let a = rng.gen_range_i32(-1_000_000, 1_000_000);
            let b = rng.gen_range_i32(-1_000_000, 1_000_000);
            for i in 0..n {
                v.push(if i % 2 == 0 { a } else { b });
            }
        }
        6 => {
            // AP sorted ascending
            let start = rng.gen_range_i32(-500_000, 500_000);
            let diff = rng.gen_range_i32(0, 500);
            for i in 0..n {
                v.push(clamp_i32(start as i64 + diff as i64 * i as i64));
            }
        }
        7 => {
            // AP sorted descending
            let start = rng.gen_range_i32(-500_000, 500_000);
            let diff = rng.gen_range_i32(-500, -1);
            for i in 0..n {
                v.push(clamp_i32(start as i64 + diff as i64 * i as i64));
            }
        }
        8 => {
            // Only two values
            for _ in 0..n {
                let pick = rng.next_u64() % 2;
                v.push(if pick == 0 { -1_000_000 } else { 1_000_000 });
            }
        }
        9 => {
            // Zero and ones
            for _ in 0..n {
                v.push(rng.gen_range_i32(-2, 2));
            }
        }
        _ => {
            // Mixed with duplicate of one element
            for _ in 0..n {
                v.push(rng.gen_range_i32(-100, 100));
            }
        }
    }
    // Ensure length in bounds (redundant)
    while v.len() < 2 {
        v.push(0);
    }
    while v.len() > 1000 {
        v.pop();
    }
    // Clamp all
    for i in 0..v.len() {
        let x = v[i] as i64;
        v[i] = clamp_i32(x);
    }
    v
}

fn print_json(arr: &[i32]) {
    // We need to output {"a":..., "b":...} per the prompt's JSON shape,
    // but the function sig is ms_merge(a, b) i.e., merge-sort merge.
    // Actually this problem is about can_make_arithmetic_progression(arr).
    // Output the array as "a" (and a dummy "b") to satisfy the required JSON format.
    // Given the ambiguity, output {"arr": [...]}
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
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match t % 7 {
            0 => 2,
            1 => 3,
            2 => 10,
            3 => 100,
            4 => 500,
            5 => 1000,
            _ => 2 + (rng.next_u64() as usize % 999),
        };
        let fillers = build_mode(&mut rng, mode, n);
        let arr = generate_test_case(&fillers);
        print_json(&arr);
    }
}