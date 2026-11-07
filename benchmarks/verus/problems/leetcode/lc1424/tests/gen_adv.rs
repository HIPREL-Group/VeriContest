use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n_rows: usize,
    row_lens: &Vec<usize>,
    values: &Vec<i32>,
) -> (nums: Vec<Vec<i32>>)
    requires
        1 <= n_rows <= 100000,
        row_lens.len() == n_rows,
        forall |i: int| 0 <= i < n_rows ==> 1 <= #[trigger] row_lens[i] <= 100000,
        values.len() == 100000,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100000,
    ensures
        1 <= nums@.len() <= 100000,
        forall |i: int| 0 <= i < nums@.len() ==>
            1 <= (#[trigger] nums@[i]).len() <= 100000,
        forall |i: int, j: int| 0 <= i < nums@.len() && 0 <= j < nums@[i].len() ==>
            1 <= (#[trigger] nums@[i][j]) <= 100000,
{
    let mut nums: Vec<Vec<i32>> = Vec::new();
    let mut idx: usize = 0;
    let vlen: usize = values.len();

    while idx < n_rows
        invariant
            1 <= n_rows <= 100000,
            row_lens.len() == n_rows,
            forall |i: int| 0 <= i < n_rows ==> 1 <= #[trigger] row_lens[i] <= 100000,
            values.len() == 100000,
            vlen == 100000,
            forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100000,
            idx <= n_rows,
            nums.len() == idx,
            forall |i: int| 0 <= i < nums@.len() ==>
                1 <= (#[trigger] nums@[i]).len() <= 100000,
            forall |i: int, j: int| 0 <= i < nums@.len() && 0 <= j < nums@[i].len() ==>
                1 <= (#[trigger] nums@[i][j]) <= 100000,
        decreases n_rows - idx,
    {
        let rlen = row_lens[idx];
        let mut row: Vec<i32> = Vec::new();
        let mut k: usize = 0;

        while k < rlen
            invariant
                1 <= rlen <= 100000,
                vlen == 100000,
                values.len() == 100000,
                forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100000,
                k <= rlen,
                row.len() == k,
                forall |j: int| 0 <= j < row@.len() ==> 1 <= #[trigger] row@[j] <= 100000,
            decreases rlen - k,
        {
            let pick = k % vlen;
            let v = values[pick];
            row.push(v);
            k = k + 1;
        }

        nums.push(row);
        idx = idx + 1;
    }

    nums
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
        self.state = self
            .state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        if lo >= hi {
            return lo;
        }
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        if lo >= hi {
            return lo;
        }
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build_values(rng: &mut Rng) -> Vec<i32> {
    let mut values: Vec<i32> = Vec::with_capacity(100000);
    for _ in 0..100000 {
        let v = rng.gen_range_i32(1, 100000);
        values.push(v);
    }
    values
}

fn pick_row_lens(rng: &mut Rng, mode: usize, n_rows: usize) -> Vec<usize> {
    let mut lens: Vec<usize> = Vec::with_capacity(n_rows);
    match mode {
        0 => {
            // All length 1
            for _ in 0..n_rows {
                lens.push(1);
            }
        }
        1 => {
            // All same small length
            let l = rng.gen_range_usize(1, 10);
            for _ in 0..n_rows {
                lens.push(l);
            }
        }
        2 => {
            // Square-ish: length == n_rows (but cap)
            let l = if n_rows > 100 { 10 } else { n_rows };
            let l = if l == 0 { 1 } else { l };
            for _ in 0..n_rows {
                lens.push(l);
            }
        }
        3 => {
            // Increasing
            for i in 0..n_rows {
                let l = (i % 20) + 1;
                lens.push(l);
            }
        }
        4 => {
            // Decreasing
            for i in 0..n_rows {
                let l = 20 - (i % 20);
                lens.push(l);
            }
        }
        5 => {
            // Mixed (like example 2)
            for i in 0..n_rows {
                let l = match i % 5 {
                    0 => 5,
                    1 => 2,
                    2 => 1,
                    3 => 3,
                    _ => 5,
                };
                lens.push(l);
            }
        }
        6 => {
            // First row very long
            for i in 0..n_rows {
                if i == 0 {
                    lens.push(10);
                } else {
                    lens.push(1);
                }
            }
        }
        7 => {
            // Last row very long
            for i in 0..n_rows {
                if i + 1 == n_rows {
                    lens.push(10);
                } else {
                    lens.push(1);
                }
            }
        }
        8 => {
            // Random small
            for _ in 0..n_rows {
                let l = rng.gen_range_usize(1, 8);
                lens.push(l);
            }
        }
        9 => {
            // Alternating 1 and bigger
            for i in 0..n_rows {
                if i % 2 == 0 {
                    lens.push(1);
                } else {
                    lens.push(6);
                }
            }
        }
        _ => {
            for _ in 0..n_rows {
                let l = rng.gen_range_usize(1, 5);
                lens.push(l);
            }
        }
    }
    lens
}

fn total_sum(lens: &Vec<usize>) -> usize {
    let mut s: usize = 0;
    for &x in lens.iter() {
        s = s.saturating_add(x);
    }
    s
}

fn cap_lens(lens: &mut Vec<usize>, cap: usize) {
    // ensure sum <= cap; each >= 1; each <= 100000
    let mut s: usize = 0;
    for i in 0..lens.len() {
        if lens[i] < 1 {
            lens[i] = 1;
        }
        if lens[i] > 100000 {
            lens[i] = 100000;
        }
        if s + lens[i] > cap {
            let remaining = if cap > s { cap - s } else { 0 };
            if remaining >= 1 {
                lens[i] = remaining;
                s += lens[i];
                // rest must be truncated - but we can't truncate (fixed length)
                // so we set them to... we need to drop them. Instead fill remaining with 1 and break
                // Actually we committed to n_rows. Set rest to... we can't, cap too small.
                // But sum must be <=100000. So truncate by shortening the vec.
                lens.truncate(i + 1);
                return;
            } else {
                lens.truncate(i);
                return;
            }
        } else {
            s += lens[i];
        }
    }
}

fn print_json(nums: &Vec<Vec<i32>>) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 {
            print!(",");
        }
        print!("[");
        for j in 0..nums[i].len() {
            if j > 0 {
                print!(",");
            }
            print!("{}", nums[i][j]);
        }
        print!("]");
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

    let values = build_values(&mut rng);

    for t in 0..total {
        let mode = t % modes;
        let n_rows = match mode {
            0 => rng.gen_range_usize(1, 100),
            1 => rng.gen_range_usize(1, 50),
            2 => rng.gen_range_usize(1, 20),
            3 => rng.gen_range_usize(5, 100),
            4 => rng.gen_range_usize(5, 100),
            5 => rng.gen_range_usize(5, 50),
            6 => rng.gen_range_usize(2, 30),
            7 => rng.gen_range_usize(2, 30),
            8 => rng.gen_range_usize(1, 200),
            9 => rng.gen_range_usize(2, 80),
            _ => rng.gen_range_usize(1, 50),
        };

        let mut row_lens = pick_row_lens(&mut rng, mode, n_rows);
        cap_lens(&mut row_lens, 100000);
        if row_lens.is_empty() {
            row_lens.push(1);
        }
        let final_n = row_lens.len();

        // Verify sum <= 100000, and each in [1, 100000], and len in [1, 100000]
        if final_n < 1 || final_n > 100000 {
            continue;
        }
        let s = total_sum(&row_lens);
        if s > 100000 {
            continue;
        }
        let mut ok = true;
        for i in 0..row_lens.len() {
            if row_lens[i] < 1 || row_lens[i] > 100000 {
                ok = false;
                break;
            }
        }
        if !ok {
            continue;
        }

        let nums = generate_test_case(final_n, &row_lens, &values);
        print_json(&nums);
    }
}