use vstd::prelude::*;

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn prefix_sum(arr: Seq<i32>, end: int) -> int
        recommends
            0 <= end <= arr.len(),
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::prefix_sum(arr, end - 1) + arr[end - 1] as int
        }
    }

    pub open spec fn total_sum(arr: Seq<i32>) -> int {
        Self::prefix_sum(arr, arr.len() as int)
    }

    pub open spec fn valid_partition(arr: Seq<i32>, a: int, b: int) -> bool {
        &&& 1 <= a < b < arr.len()
        &&& {
            let s1 = Self::prefix_sum(arr, a);
            let s2 = Self::prefix_sum(arr, b) - Self::prefix_sum(arr, a);
            let s3 = Self::total_sum(arr) - Self::prefix_sum(arr, b);
            s1 == s2 && s2 == s3
        }
    }

    pub fn can_three_parts_equal_sum(arr: Vec<i32>) -> (result: bool)
        requires
            3 <= arr.len() <= 50_000,
            forall |i: int| 0 <= i < arr.len() ==> -10_000 <= #[trigger] arr[i] <= 10_000,
        ensures
            result == (exists |a: int, b: int| Self::valid_partition(arr@, a, b)),
    {
        assume(false);
        false
    }
}

pub fn generate_test_case(
    x: i32,
    y: i32,
    z: i32,
    nx: usize,
    ny: usize,
    nz: usize,
) -> (arr: Vec<i32>)
    requires
        1 <= nx <= 16_666,
        1 <= ny <= 16_666,
        1 <= nz <= 16_666,
        nx + ny + nz <= 50_000,
        -10_000 <= x <= 10_000,
        -10_000 <= y <= 10_000,
        -10_000 <= z <= 10_000,
    ensures
        3 <= arr.len() <= 50_000,
        forall |i: int| 0 <= i < arr.len() ==> -10_000 <= #[trigger] arr[i] <= 10_000,
{
    let mut arr: Vec<i32> = Vec::new();

    let mut i: usize = 0;
    while i < nx
        invariant
            0 <= i <= nx,
            arr.len() == i,
            1 <= nx <= 16_666,
            1 <= ny <= 16_666,
            1 <= nz <= 16_666,
            nx + ny + nz <= 50_000,
            -10_000 <= x <= 10_000,
            -10_000 <= y <= 10_000,
            -10_000 <= z <= 10_000,
            forall |k: int| 0 <= k < arr.len() ==> #[trigger] arr[k] == x,
            forall |k: int| 0 <= k < arr.len() ==> -10_000 <= #[trigger] arr[k] <= 10_000,
        decreases nx - i,
    {
        arr.push(x);
        i = i + 1;
    }

    let base1 = arr.len();
    let mut j: usize = 0;
    while j < ny
        invariant
            base1 == nx,
            0 <= j <= ny,
            arr.len() == base1 + j,
            1 <= nx <= 16_666,
            1 <= ny <= 16_666,
            1 <= nz <= 16_666,
            nx + ny + nz <= 50_000,
            -10_000 <= x <= 10_000,
            -10_000 <= y <= 10_000,
            -10_000 <= z <= 10_000,
            forall |k: int| 0 <= k < base1 as int ==> #[trigger] arr[k] == x,
            forall |k: int| base1 as int <= k < arr.len() ==> #[trigger] arr[k] == y,
            forall |k: int| 0 <= k < arr.len() ==> -10_000 <= #[trigger] arr[k] <= 10_000,
        decreases ny - j,
    {
        arr.push(y);
        j = j + 1;
    }

    let base2 = arr.len();
    let mut k: usize = 0;
    while k < nz
        invariant
            base1 == nx,
            base2 == nx + ny,
            0 <= k <= nz,
            arr.len() == base2 + k,
            1 <= nx <= 16_666,
            1 <= ny <= 16_666,
            1 <= nz <= 16_666,
            nx + ny + nz <= 50_000,
            -10_000 <= x <= 10_000,
            -10_000 <= y <= 10_000,
            -10_000 <= z <= 10_000,
            forall |t: int| 0 <= t < base1 as int ==> #[trigger] arr[t] == x,
            forall |t: int| base1 as int <= t < base2 as int ==> #[trigger] arr[t] == y,
            forall |t: int| base2 as int <= t < arr.len() ==> #[trigger] arr[t] == z,
            forall |t: int| 0 <= t < arr.len() ==> -10_000 <= #[trigger] arr[t] <= 10_000,
        decreases nz - k,
    {
        arr.push(z);
        k = k + 1;
    }

    assert(arr.len() == nx + ny + nz);
    assert(3 <= arr.len());
    assert(arr.len() <= 50_000);
    arr
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

fn choose_lengths(rng: &mut Rng, total: usize) -> (usize, usize, usize) {
    assert!(3 <= total && total <= 50_000);
    let a = rng.gen_range_usize(1, total - 2);
    let b = rng.gen_range_usize(1, total - a - 1);
    let c = total - a - b;
    (a, b, c)
}

fn build_case_for_mode(rng: &mut Rng, mode: usize) -> Vec<i32> {
    match mode {
        0 => {
            let total = 3;
            let (a, b, c) = choose_lengths(rng, total);
            generate_test_case(0, 0, 0, a, b, c)
        }
        1 => {
            let total = 49_998;
            let (a, b, c) = choose_lengths(rng, total);
            generate_test_case(0, 0, 0, a, b, c)
        }
        2 => {
            let total = rng.gen_range_usize(3, 40);
            let (a, b, c) = choose_lengths(rng, total);
            generate_test_case(10_000, -10_000, 0, a, b, c)
        }
        3 => {
            let total = rng.gen_range_usize(3, 200);
            let (a, b, c) = choose_lengths(rng, total);
            generate_test_case(10_000, 10_000, 10_000, a, b, c)
        }
        4 => {
            let total = rng.gen_range_usize(3, 200);
            let (a, b, c) = choose_lengths(rng, total);
            generate_test_case(-10_000, -10_000, -10_000, a, b, c)
        }
        5 => {
            let total = rng.gen_range_usize(3, 5000);
            let x = rng.gen_range_i32(-3, 3);
            let y = rng.gen_range_i32(-3, 3);
            let z = rng.gen_range_i32(-3, 3);
            let (a, b, c) = choose_lengths(rng, total);
            generate_test_case(x, y, z, a, b, c)
        }
        6 => {
            let total = rng.gen_range_usize(3, 5000);
            let (a, b, c) = (1usize, 1usize, total - 2);
            generate_test_case(7, -7, 0, a, b, c)
        }
        7 => {
            let total = rng.gen_range_usize(3, 5000);
            let (a, b, c) = (total - 2, 1usize, 1usize);
            generate_test_case(1, 2, 3, a, b, c)
        }
        8 => {
            let total = rng.gen_range_usize(3, 5000);
            let a = 1usize;
            let b = 1usize;
            let c = total - 2;
            generate_test_case(0, 1, -1, a, b, c)
        }
        9 => {
            let total = rng.gen_range_usize(3, 49_998);
            let (a, b, c) = choose_lengths(rng, total);
            generate_test_case(9999, -9999, 1, a, b, c)
        }
        10 => {
            let total = rng.gen_range_usize(3, 49_998);
            let (a, b, c) = choose_lengths(rng, total);
            generate_test_case(10_000, 0, -10_000, a, b, c)
        }
        11 => {
            let total = rng.gen_range_usize(3, 49_998);
            let (a, b, c) = choose_lengths(rng, total);
            generate_test_case(123, 123, 123, a, b, c)
        }
        12 => {
            let total = rng.gen_range_usize(3, 49_998);
            let a = 1usize;
            let b = total - 2;
            let c = 1usize;
            generate_test_case(-1, 0, 1, a, b, c)
        }
        13 => {
            let total = rng.gen_range_usize(3, 49_998);
            let a = total / 2;
            let b = 1usize;
            let c = total - a - b;
            generate_test_case(42, -42, 42, a, b, c)
        }
        _ => {
            let total = rng.gen_range_usize(3, 49_998);
            let (a, b, c) = choose_lengths(rng, total);
            let x = rng.gen_range_i32(-10_000, 10_000);
            let y = rng.gen_range_i32(-10_000, 10_000);
            let z = rng.gen_range_i32(-10_000, 10_000);
            generate_test_case(x, y, z, a, b, c)
        }
    }
}

fn print_json_array(arr: &[i32]) {
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
    let seed = std::env::args()
        .nth(1)
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(1);

    let mut rng = Rng::new(seed);
    let total_cases = 200usize;

    for t in 0..total_cases {
        let mode = if t < 140 {
            t % 14
        } else {
            14 + (rng.next_u64() as usize % 6)
        };
        let arr = build_case_for_mode(&mut rng, mode);
        print_json_array(&arr);
    }
}