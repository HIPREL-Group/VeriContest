use vstd::prelude::*;

verus! {

pub fn generate_test_case(raw_a: Vec<i32>, raw_b: Vec<i32>) -> (result: (Vec<i32>, Vec<i32>))
    ensures 2 <= result.0.len() <= 100000, result.0.len() == result.1.len(),
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 200000,
        forall|i: int| 0 <= i < result.1.len() ==> 0 <= #[trigger] result.1[i] <= 200000,
        forall|i: int| 1 <= i < result.0.len() ==>
            ((#[trigger] result.0[i] > result.0[i - 1] && result.1[i] > result.1[i - 1])
            || (result.0[i] > result.1[i - 1] && result.1[i] > result.0[i - 1])),
{
    let n = if raw_a.len() < 2 { 2usize } else if raw_a.len() > 100000 { 100000usize } else { raw_a.len() };
    let mut a: Vec<i32> = Vec::new();
    let mut b: Vec<i32> = Vec::new();
    let mut low_previous = -1i32;
    let mut high_previous = -1i32;
    let mut i = 0usize;
    while i < n
        invariant i <= n, 2 <= n <= 100000, a.len() == i, b.len() == i,
            -1 <= low_previous <= high_previous <= 200000 - (n - i),
            i == 0 ==> low_previous == -1 && high_previous == -1,
            i > 0 ==> ((low_previous == a[i - 1] && high_previous == b[i - 1])
                || (low_previous == b[i - 1] && high_previous == a[i - 1])),
            forall|j: int| 0 <= j < i ==> 0 <= #[trigger] a[j] <= 200000,
            forall|j: int| 0 <= j < i ==> 0 <= #[trigger] b[j] <= 200000,
            forall|j: int| 1 <= j < i ==>
                ((#[trigger] a[j] > a[j - 1] && b[j] > b[j - 1])
                || (a[j] > b[j - 1] && b[j] > a[j - 1])),
        decreases n - i,
    {
        let x = if i < raw_a.len() { raw_a[i] } else { 0 };
        let y = if i < raw_b.len() { raw_b[i] } else { 0 };
        let swapped = x > y;
        let low = if x < y { x } else { y };
        let high = if x < y { y } else { x };
        let ceiling = 200000 - ((n - i - 1) as i32);
        let low = if low <= low_previous { low_previous + 1 } else if low > ceiling { ceiling } else { low };
        let high = if high <= high_previous { high_previous + 1 } else if high > ceiling { ceiling } else { high };
        let high = if high < low { low } else { high };
        a.push(if swapped { high } else { low });
        b.push(if swapped { low } else { high });
        low_previous = low;
        high_previous = high;
        i += 1;
    }
    (a, b)
}


pub fn generate_candidate(
    nums1: Vec<i32>,
    nums2: Vec<i32>,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        2 <= nums1.len() <= 100_000,
        nums1.len() == nums2.len(),
        forall|i: int| 0 <= i < nums1.len() ==> 0 <= #[trigger] nums1[i] <= 200_000,
        forall|i: int| 0 <= i < nums2.len() ==> 0 <= #[trigger] nums2[i] <= 200_000,
    ensures
        2 <= result.0.len() <= 100_000,
        result.0.len() == result.1.len(),
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i],
        forall|i: int| 0 <= i < result.1.len() ==> 0 <= #[trigger] result.1[i],
{
    (nums1, nums2)
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
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_mode(rng: &mut Rng, mode: usize, n: usize) -> (Vec<i32>, Vec<i32>) {
    let mut nums1 = Vec::with_capacity(n);
    let mut nums2 = Vec::with_capacity(n);
    match mode {
        0 => {
            // Already strictly increasing both, 0 swaps
            for i in 0..n {
                nums1.push(i as i32);
                nums2.push((i as i32) + 100);
            }
        }
        1 => {
            // Need to swap every position
            for i in 0..n {
                // Make so nums1 keeps increasing by swapping
                // Place value 2*i in nums2 and 2*i+1 in nums1 swapped
                nums1.push((2 * i + 1) as i32);
                nums2.push((2 * i) as i32);
            }
            // This is actually already increasing; make it trickier:
            for i in 0..n {
                nums1[i] = if i % 2 == 0 { (2*i) as i32 } else { (2*i - 1) as i32 };
                nums2[i] = if i % 2 == 0 { (2*i + 1) as i32 } else { (2*i) as i32 };
            }
        }
        2 => {
            // random small values but ensure a solution exists by interleaving
            for i in 0..n {
                let a = rng.gen_range_i32(0, 200_000);
                let b = rng.gen_range_i32(0, 200_000);
                nums1.push(a);
                nums2.push(b);
            }
            // Ensure a solution exists: overwrite with a constructed valid pair
            let mut a_prev: i32 = -1;
            let mut b_prev: i32 = -1;
            for i in 0..n {
                let step_a = rng.gen_range_i32(1, 3);
                let step_b = rng.gen_range_i32(1, 3);
                let a = a_prev + step_a;
                let b = b_prev + step_b;
                if (a as i64) > 200_000 || (b as i64) > 200_000 {
                    nums1[i] = a_prev + 1;
                    nums2[i] = b_prev + 1;
                } else {
                    // sometimes swap them
                    if rng.next_u64() % 2 == 0 {
                        nums1[i] = a;
                        nums2[i] = b;
                    } else {
                        nums1[i] = b;
                        nums2[i] = a;
                    }
                }
                a_prev = nums1[i];
                b_prev = nums2[i];
                if a_prev > 200_000 { a_prev = 200_000; nums1[i] = 200_000; }
                if b_prev > 200_000 { b_prev = 200_000; nums2[i] = 200_000; }
            }
        }
        3 => {
            // Example 1: [1,3,5,4] [1,2,3,7]
            let a = [1i32, 3, 5, 4];
            let b = [1i32, 2, 3, 7];
            for i in 0..n {
                nums1.push(a[i % 4] + (i / 4) as i32 * 8);
                nums2.push(b[i % 4] + (i / 4) as i32 * 8);
            }
        }
        4 => {
            // Many ties boundary - values near each other
            let mut a_prev: i32 = 0;
            let mut b_prev: i32 = 0;
            for i in 0..n {
                let a = a_prev + 1;
                let b = b_prev + 1;
                if rng.next_u64() % 3 == 0 {
                    nums1.push(b);
                    nums2.push(a);
                } else {
                    nums1.push(a);
                    nums2.push(b);
                }
                a_prev = if nums1[i] > a_prev { nums1[i] } else { a_prev + 1 };
                b_prev = if nums2[i] > b_prev { nums2[i] } else { b_prev + 1 };
            }
        }
        5 => {
            // Equal arrays strictly increasing
            for i in 0..n {
                nums1.push(i as i32);
                nums2.push(i as i32);
            }
        }
        6 => {
            // Large n
            for i in 0..n {
                nums1.push((i * 2) as i32);
                nums2.push((i * 2 + 1) as i32);
            }
        }
        7 => {
            // Values at maximum
            let base = 200_000 - (n as i32);
            for i in 0..n {
                nums1.push(base + i as i32);
                nums2.push(base + i as i32);
            }
        }
        8 => {
            // Minimum length
            nums1.push(1);
            nums2.push(2);
            for _ in 1..n {
                nums1.push(nums1[nums1.len()-1] + 1);
                nums2.push(nums2[nums2.len()-1] + 1);
            }
        }
        9 => {
            // Random with guaranteed solution (keep both strictly increasing)
            let mut a_prev: i32 = -1;
            let mut b_prev: i32 = -1;
            for _ in 0..n {
                let sa = rng.gen_range_i32(1, 5);
                let sb = rng.gen_range_i32(1, 5);
                let mut a = a_prev + sa;
                let mut b = b_prev + sb;
                if a > 200_000 { a = 200_000; }
                if b > 200_000 { b = 200_000; }
                if rng.next_u64() % 2 == 0 {
                    nums1.push(a); nums2.push(b);
                } else {
                    nums1.push(b); nums2.push(a);
                }
                a_prev = a;
                b_prev = b;
            }
        }
        _ => {
            for i in 0..n {
                nums1.push(i as i32);
                nums2.push(i as i32);
            }
        }
    }
    // Clamp to [0, 200000]
    for i in 0..n {
        if nums1[i] < 0 { nums1[i] = 0; }
        if nums1[i] > 200_000 { nums1[i] = 200_000; }
        if nums2[i] < 0 { nums2[i] = 0; }
        if nums2[i] > 200_000 { nums2[i] = 200_000; }
    }
    (nums1, nums2)
}

fn print_json(nums1: &[i32], nums2: &[i32]) {
    let (nums1, nums2) = generate_test_case(nums1.to_vec(), nums2.to_vec());
    print!("{{\"nums1\":[");
    for i in 0..nums1.len() {
        if i > 0 { print!(","); }
        print!("{}", nums1[i]);
    }
    print!("],\"nums2\":[");
    for i in 0..nums2.len() {
        if i > 0 { print!(","); }
        print!("{}", nums2[i]);
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
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => 2 + (t % 20),
            1 => 4 + (t % 10),
            2 => 5 + (t % 50),
            3 => 4 + 4 * (t % 5),
            4 => 10 + (t % 30),
            5 => 2 + (t % 100),
            6 => 1000 + (t % 50),
            7 => 2 + (t % 15),
            8 => 2,
            9 => 50 + (t % 200),
            _ => 10,
        };
        let n = if n < 2 { 2 } else if n > 100_000 { 100_000 } else { n };
        let (nums1, nums2) = build_mode(&mut rng, mode, n);
        let (n1, n2) = generate_candidate(nums1, nums2);
        print_json(&n1, &n2);
    }
}
