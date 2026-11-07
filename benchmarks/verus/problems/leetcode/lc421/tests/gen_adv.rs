use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 200_000,
        forall |i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= i32::MAX,
    ensures
        1 <= nums.len() <= 200_000,
        forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= i32::MAX,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut pos: usize = 0;
    while pos < n
        invariant
            n == values.len(),
            1 <= n <= 200_000,
            0 <= pos <= n,
            nums.len() == pos,
            forall |k: int| 0 <= k < pos as int ==> #[trigger] nums[k] == values[k],
            forall |k: int| 0 <= k < values.len() ==> 0 <= #[trigger] values[k] <= i32::MAX,
        decreases n - pos,
    {
        nums.push(values[pos]);
        pos = pos + 1;
    }
    nums
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

    fn gen_i32_nonneg(&mut self, hi: i32) -> i32 {
        let v = (self.next_u64() as u64) % ((hi as u64) + 1);
        v as i32
    }
}

fn print_json(nums: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", nums[i]);
    }
    println!("]}}");
}

fn build_and_emit(values: Vec<i32>) {
    let nums = generate_test_case(&values);
    print_json(&nums);
}

fn mode_random_small(rng: &mut Rng) -> Vec<i32> {
    let n = rng.gen_range_usize(1, 20);
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_i32_nonneg(100));
    }
    v
}

fn mode_random_medium(rng: &mut Rng) -> Vec<i32> {
    let n = rng.gen_range_usize(50, 500);
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_i32_nonneg(i32::MAX));
    }
    v
}

fn mode_all_same(rng: &mut Rng) -> Vec<i32> {
    let n = rng.gen_range_usize(1, 300);
    let x = rng.gen_i32_nonneg(i32::MAX);
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(x);
    }
    v
}

fn mode_all_zero(rng: &mut Rng) -> Vec<i32> {
    let n = rng.gen_range_usize(1, 300);
    vec![0i32; n]
}

fn mode_single(rng: &mut Rng) -> Vec<i32> {
    vec![rng.gen_i32_nonneg(i32::MAX)]
}

fn mode_powers_of_two(rng: &mut Rng) -> Vec<i32> {
    let n = rng.gen_range_usize(2, 31);
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        v.push(1i32 << (i as u32 % 31));
    }
    v
}

fn mode_max_and_zero() -> Vec<i32> {
    vec![0, i32::MAX, i32::MAX, 0, 1, i32::MAX - 1]
}

fn mode_sequential(rng: &mut Rng) -> Vec<i32> {
    let n = rng.gen_range_usize(1, 200);
    let start = rng.gen_i32_nonneg(1000);
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        v.push(start + i as i32);
    }
    v
}

fn mode_large(rng: &mut Rng) -> Vec<i32> {
    let n = 200_000usize;
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_i32_nonneg(i32::MAX));
    }
    v
}

fn mode_bit_variants(rng: &mut Rng) -> Vec<i32> {
    let n = rng.gen_range_usize(2, 64);
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        let bits = rng.gen_range_usize(0, 31);
        let mut x: i32 = 0;
        for _ in 0..bits {
            let b = rng.gen_range_usize(0, 30);
            x |= 1i32 << (b as u32);
        }
        v.push(x);
    }
    v
}

fn mode_two_clusters(rng: &mut Rng) -> Vec<i32> {
    let n = rng.gen_range_usize(4, 100);
    let a = rng.gen_i32_nonneg(i32::MAX);
    let b = rng.gen_i32_nonneg(i32::MAX);
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        if i % 2 == 0 { v.push(a); } else { v.push(b); }
    }
    v
}

fn mode_example1() -> Vec<i32> {
    vec![3, 10, 5, 25, 2, 8]
}

fn mode_example2() -> Vec<i32> {
    vec![14,70,53,83,49,91,36,80,92,51,66,70]
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

    build_and_emit(mode_example1());
    build_and_emit(mode_example2());
    build_and_emit(mode_max_and_zero());

    for t in 0..total {
        let mode = t % 11;
        let v = match mode {
            0 => mode_random_small(&mut rng),
            1 => mode_random_medium(&mut rng),
            2 => mode_all_same(&mut rng),
            3 => mode_all_zero(&mut rng),
            4 => mode_single(&mut rng),
            5 => mode_powers_of_two(&mut rng),
            6 => mode_sequential(&mut rng),
            7 => mode_bit_variants(&mut rng),
            8 => mode_two_clusters(&mut rng),
            9 => {
                if t % 33 == 9 {
                    mode_large(&mut rng)
                } else {
                    mode_random_medium(&mut rng)
                }
            }
            _ => {
                let n = rng.gen_range_usize(1, 1000);
                let mut v = Vec::with_capacity(n);
                for _ in 0..n {
                    v.push(rng.gen_i32_nonneg(i32::MAX));
                }
                v
            }
        };
        build_and_emit(v);
    }
}