use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 100,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100,
    ensures
        1 <= nums.len() <= 100,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            nums.len() == i,
            forall |k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 100,
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 100,
        decreases n - i,
    {
        nums.push(values[i]);
        i = i + 1;
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

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn clamp_vec(v: &mut Vec<i32>) {
    for x in v.iter_mut() {
        if *x < 1 { *x = 1; }
        if *x > 100 { *x = 100; }
    }
}

fn mode_random(rng: &mut Rng) -> Vec<i32> {
    let n = rng.gen_range_usize(1, 100);
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i32(1, 100));
    }
    v
}

fn mode_sorted(rng: &mut Rng) -> Vec<i32> {
    let n = rng.gen_range_usize(1, 100);
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i32(1, 100));
    }
    v.sort();
    v
}

fn mode_sorted_rotated(rng: &mut Rng) -> Vec<i32> {
    let n = rng.gen_range_usize(1, 100);
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i32(1, 100));
    }
    v.sort();
    let r = rng.gen_range_usize(0, n - 1);
    let mut rotated = Vec::with_capacity(n);
    for i in 0..n {
        rotated.push(v[(i + r) % n]);
    }
    rotated
}

fn mode_all_same(rng: &mut Rng) -> Vec<i32> {
    let n = rng.gen_range_usize(1, 100);
    let x = rng.gen_range_i32(1, 100);
    vec![x; n]
}

fn mode_reverse_sorted(rng: &mut Rng) -> Vec<i32> {
    let n = rng.gen_range_usize(2, 100);
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i32(1, 100));
    }
    v.sort();
    v.reverse();
    v
}

fn mode_two_descents(rng: &mut Rng) -> Vec<i32> {
    // Sorted then rotated but with extra descent
    let mut v = mode_sorted_rotated(rng);
    if v.len() >= 3 {
        let i = rng.gen_range_usize(1, v.len() - 2);
        v[i] = 100;
        v[i + 1] = 1;
    }
    v
}

fn mode_single(rng: &mut Rng) -> Vec<i32> {
    vec![rng.gen_range_i32(1, 100)]
}

fn mode_two(rng: &mut Rng) -> Vec<i32> {
    vec![rng.gen_range_i32(1, 100), rng.gen_range_i32(1, 100)]
}

fn mode_boundary(rng: &mut Rng) -> Vec<i32> {
    let n = 100;
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        if rng.next_u64() % 2 == 0 {
            v.push(1);
        } else {
            v.push(100);
        }
    }
    v
}

fn mode_duplicates_sorted(rng: &mut Rng) -> Vec<i32> {
    let n = rng.gen_range_usize(3, 100);
    let mut v = Vec::with_capacity(n);
    let low = rng.gen_range_i32(1, 50);
    for _ in 0..n / 2 {
        v.push(low);
    }
    let high = rng.gen_range_i32(low, 100);
    while v.len() < n {
        v.push(high);
    }
    // optional rotate
    let r = rng.gen_range_usize(0, n - 1);
    let mut rot = Vec::with_capacity(n);
    for i in 0..n {
        rot.push(v[(i + r) % n]);
    }
    rot
}

fn print_json(nums: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
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
    let total = 200usize;

    for t in 0..total {
        let mode = t % 10;
        let mut v = match mode {
            0 => mode_random(&mut rng),
            1 => mode_sorted(&mut rng),
            2 => mode_sorted_rotated(&mut rng),
            3 => mode_all_same(&mut rng),
            4 => mode_reverse_sorted(&mut rng),
            5 => mode_two_descents(&mut rng),
            6 => mode_single(&mut rng),
            7 => mode_two(&mut rng),
            8 => mode_boundary(&mut rng),
            _ => mode_duplicates_sorted(&mut rng),
        };
        clamp_vec(&mut v);
        if v.is_empty() { v.push(1); }
        if v.len() > 100 { v.truncate(100); }
        let nums = generate_test_case(&v);
        print_json(&nums);
    }
}