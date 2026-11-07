use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    pos1: usize,
    posn: usize,
    perm: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        2 <= n <= 50,
        perm.len() == n,
        pos1 < n,
        posn < n,
        pos1 != posn,
        perm[pos1 as int] == 1,
        perm[posn as int] == n as i32,
        forall |i: int| 0 <= i < n ==> 1 <= #[trigger] perm[i] <= n,
        forall |i: int, j: int| 0 <= i < j < n ==> perm[i] != perm[j],
    ensures
        nums.len() == n,
        2 <= nums.len() <= 50,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= nums.len(),
        forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] != nums[j],
        exists |i: int| 0 <= i < nums.len() && nums[i] == 1,
        exists |i: int| 0 <= i < nums.len() && nums[i] == nums.len() as i32,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            2 <= n <= 50,
            perm.len() == n,
            i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < i as int ==> nums[k] == perm[k],
        decreases n - i,
    {
        nums.push(perm[i]);
        i += 1;
    }

    proof {
        assert(nums.len() == n);
        assert forall |k: int| 0 <= k < nums.len() implies 1 <= #[trigger] nums[k] <= nums.len() by {
            assert(nums[k] == perm[k]);
        }
        assert forall |a: int, b: int| 0 <= a < b < nums.len() implies nums[a] != nums[b] by {
            assert(nums[a] == perm[a]);
            assert(nums[b] == perm[b]);
        }
        assert(nums[pos1 as int] == 1);
        assert(nums[posn as int] == n as i32);
    }

    nums
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
    fn gen_range(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
}

fn make_permutation(rng: &mut Rng, n: usize, pos1: usize, posn: usize) -> Vec<i32> {
    // Build a permutation of 1..=n with 1 at pos1 and n at posn
    let mut remaining: Vec<i32> = Vec::new();
    for v in 2..n as i32 {
        remaining.push(v);
    }
    // shuffle
    let len = remaining.len();
    for i in (1..len).rev() {
        let j = rng.gen_range(0, i);
        remaining.swap(i, j);
    }

    let mut result: Vec<i32> = Vec::with_capacity(n);
    for _ in 0..n {
        result.push(0);
    }
    result[pos1] = 1;
    result[posn] = n as i32;
    let mut ri = 0usize;
    for k in 0..n {
        if k != pos1 && k != posn {
            result[k] = remaining[ri];
            ri += 1;
        }
    }
    result
}

fn pick_positions(rng: &mut Rng, mode: usize, n: usize) -> (usize, usize) {
    match mode {
        0 => (0, n - 1),                 // already semi-ordered
        1 => (n - 1, 0),                 // worst case
        2 => (0, 0),                     // will be adjusted
        3 => (1, n - 1),
        4 => (0, n - 2),
        5 => (n / 2, n / 2 + 1),
        6 => {
            let a = rng.gen_range(0, n - 1);
            let mut b = rng.gen_range(0, n - 2);
            if b >= a { b += 1; }
            (a, b)
        }
        7 => (n - 2, n - 1),
        8 => (0, 1),
        _ => {
            let a = rng.gen_range(0, n - 1);
            let mut b = rng.gen_range(0, n - 2);
            if b >= a { b += 1; }
            (a, b)
        }
    }
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
    let modes = 10usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n: usize = match mode {
            0 => 2 + (t % 5),
            1 => 50,
            2 => 3 + (t % 10),
            3 => 49,
            4 => 10,
            5 => 25,
            6 => 2 + (t % 49),
            7 => 50,
            8 => 5 + (t % 20),
            _ => 2 + (rng.next_u64() as usize % 49),
        };
        let n = if n < 2 { 2 } else if n > 50 { 50 } else { n };

        let (mut pos1, mut posn) = pick_positions(&mut rng, mode, n);
        if pos1 >= n { pos1 = n - 1; }
        if posn >= n { posn = n - 1; }
        if pos1 == posn {
            if posn == 0 { posn = 1; } else { posn = pos1 - 1; }
        }

        let perm = make_permutation(&mut rng, n, pos1, posn);
        let nums = generate_test_case(n, pos1, posn, &perm);
        print_json(&nums);
    }
}