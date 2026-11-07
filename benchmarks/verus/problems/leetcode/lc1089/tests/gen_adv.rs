use vstd::prelude::*;

verus! {

proof fn strictly_increasing_bound(seq: Seq<usize>, from: int, to: int, base: int)
    requires
        0 <= from < to,
        to <= seq.len(),
        seq[from] as int >= base,
        forall|i: int, j: int| from <= i < j < to ==> seq[i] < seq[j],
    ensures
        seq[to - 1] as int >= base + (to - from - 1),
    decreases to - from,
{
    if to - from <= 1 {
    } else {
        assert(seq[from] < seq[from + 1]);
        strictly_increasing_bound(seq, from + 1, to, base + 1);
    }
}

pub fn generate_test_case(
    len: usize,
    zero_positions: &Vec<usize>,
    fillers: &Vec<i32>,
) -> (arr: Vec<i32>)
    requires
        1 <= len <= 10_000,
        zero_positions.len() <= len,
        fillers.len() + zero_positions.len() == len,
        forall|i: int| 0 <= i < zero_positions.len() ==> #[trigger] zero_positions[i] < len,
        forall|i: int, j: int|
            0 <= i < j < zero_positions.len() ==> #[trigger] zero_positions[i] < #[trigger] zero_positions[j],
        forall|i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 9,
    ensures
        arr.len() == len,
        1 <= arr.len() <= 10_000,
        forall|i: int| 0 <= i < arr.len() ==> 0 <= #[trigger] arr[i] <= 9,
{
    let mut arr: Vec<i32> = Vec::new();
    let mut pos: usize = 0;
    let mut zi: usize = 0;
    let mut fi: usize = 0;

    while pos < len
        invariant
            1 <= len <= 10_000,
            0 <= pos <= len,
            arr.len() == pos,
            0 <= zi <= zero_positions.len(),
            0 <= fi <= fillers.len(),
            zi + fi == pos,
            zero_positions.len() <= len,
            fillers.len() + zero_positions.len() == len,
            forall|i: int| 0 <= i < zero_positions.len() ==> #[trigger] zero_positions[i] < len,
            forall|i: int, j: int|
                0 <= i < j < zero_positions.len() ==> #[trigger] zero_positions[i] < #[trigger] zero_positions[j],
            forall|i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 9,
            forall|k: int| 0 <= k < pos as int ==> 0 <= #[trigger] arr[k] <= 9,
            forall|j: int| 0 <= j < zi as int ==> #[trigger] zero_positions[j] < pos,
            forall|j: int| zi as int <= j < zero_positions.len() as int ==> pos <= #[trigger] zero_positions[j],
        decreases len - pos,
    {
        if zi < zero_positions.len() && zero_positions[zi] == pos {
            arr.push(0);
            proof {
                assert forall|j: int| 0 <= j < (zi + 1) as int
                    implies #[trigger] zero_positions[j] < (pos + 1) as int by {
                    if j == zi as int {
                        assert(zero_positions[j] == pos);
                    }
                };
                assert forall|j: int|
                    (zi + 1) as int <= j && j < zero_positions.len() as int
                implies
                    (pos + 1) as int <= #[trigger] zero_positions[j]
                by {
                    assert(zero_positions[zi as int] < zero_positions[j]);
                };
            }
            zi = zi + 1;
        } else {
            proof {
                if zi < zero_positions.len() {
                    assert(zero_positions[zi as int] != pos);
                    assert(pos <= zero_positions[zi as int]);
                    assert(pos < zero_positions[zi as int]);
                    strictly_increasing_bound(
                        zero_positions@,
                        zi as int,
                        zero_positions.len() as int,
                        (pos + 1) as int,
                    );
                    let last = zero_positions.len() as int - 1;
                    assert(zero_positions@[last] as int
                        >= (pos as int + 1) + (zero_positions.len() as int - zi as int - 1));
                    assert(zero_positions@[last] < len);
                }
                assert(fi < fillers.len());
            }
            arr.push(fillers[fi]);
            proof {
                assert forall|j: int| 0 <= j < zi as int
                    implies #[trigger] zero_positions[j] < (pos + 1) as int by {};
                assert forall|j: int|
                    zi as int <= j && j < zero_positions.len() as int
                implies
                    (pos + 1) as int <= #[trigger] zero_positions[j]
                by {
                    assert(pos < zero_positions[zi as int]);
                    if j > zi as int {
                        assert(zero_positions[zi as int] < zero_positions[j]);
                    }
                };
            }
            fi = fi + 1;
        }
        pos = pos + 1;
    }

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

fn make_fillers(count: usize, rng: &mut Rng, mode: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(count);
    match mode {
        0 => {
            for _ in 0..count {
                v.push(1);
            }
        }
        1 => {
            for i in 0..count {
                v.push(((i % 9) + 1) as i32);
            }
        }
        2 => {
            for i in 0..count {
                v.push((9 - (i % 9)) as i32);
            }
        }
        3 => {
            for _ in 0..count {
                v.push(9);
            }
        }
        _ => {
            for _ in 0..count {
                v.push(rng.gen_range_i32(1, 9));
            }
        }
    }
    v
}

fn make_zero_positions(len: usize, zero_count: usize, rng: &mut Rng, mode: usize) -> Vec<usize> {
    let mut z = Vec::with_capacity(zero_count);
    match mode {
        0 => {}
        1 => {
            for i in 0..zero_count {
                z.push(i);
            }
        }
        2 => {
            for i in 0..zero_count {
                z.push(len - zero_count + i);
            }
        }
        3 => {
            let mut i = 0usize;
            while i < zero_count {
                z.push(i * 2);
                i += 1;
            }
        }
        4 => {
            let mut i = 0usize;
            while i < zero_count {
                z.push(len - 1 - i * 2);
                i += 1;
            }
            z.sort();
        }
        5 => {
            if zero_count > 0 {
                z.push(0);
            }
            if zero_count > 1 {
                z.push(len - 1);
            }
            let mut used = vec![false; len];
            if zero_count > 0 {
                used[0] = true;
            }
            if zero_count > 1 {
                used[len - 1] = true;
            }
            while z.len() < zero_count {
                let p = rng.gen_range_usize(0, len - 1);
                if !used[p] {
                    used[p] = true;
                    z.push(p);
                }
            }
            z.sort();
        }
        6 => {
            let mut used = vec![false; len];
            while z.len() < zero_count {
                let p = rng.gen_range_usize(0, len - 1);
                if !used[p] {
                    used[p] = true;
                    z.push(p);
                }
            }
            z.sort();
        }
        7 => {
            let start = if len > zero_count { (len - zero_count) / 2 } else { 0 };
            for i in 0..zero_count {
                z.push(start + i);
            }
        }
        8 => {
            let mut cur = 0usize;
            for _ in 0..zero_count {
                z.push(cur);
                cur += 3;
                if cur >= len {
                    cur = (cur % 3) + 1;
                    while cur < len && z.contains(&cur) {
                        cur += 3;
                    }
                }
            }
            z.sort();
            z.dedup();
            let mut used = vec![false; len];
            for &p in &z {
                used[p] = true;
            }
            while z.len() < zero_count {
                let p = rng.gen_range_usize(0, len - 1);
                if !used[p] {
                    used[p] = true;
                    z.push(p);
                }
            }
            z.sort();
        }
        _ => {
            let mut used = vec![false; len];
            while z.len() < zero_count {
                let p = rng.gen_range_usize(0, len - 1);
                if !used[p] {
                    used[p] = true;
                    z.push(p);
                }
            }
            z.sort();
        }
    }
    z
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

    let total = 200usize;
    let modes = 10usize;

    for t in 0..total {
        let mode = t % modes;
        let len = match mode {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => 8,
            4 => 16,
            5 => 31,
            6 => 64,
            7 => 257,
            8 => 1024,
            _ => {
                if t % 3 == 0 {
                    10_000
                } else {
                    rng.gen_range_usize(1, 10_000)
                }
            }
        };

        let zero_count = match mode {
            0 => 0,
            1 => len,
            2 => 1.min(len),
            3 => len / 2,
            4 => (len * 3) / 4,
            5 => len.saturating_sub(1),
            6 => len / 3,
            7 => len / 4,
            8 => len / 5,
            _ => rng.gen_range_usize(0, len),
        };

        let zero_positions = make_zero_positions(len, zero_count, &mut rng, mode);
        let fillers = make_fillers(len - zero_count, &mut rng, mode);
        let arr = generate_test_case(len, &zero_positions, &fillers);
        print_json(&arr);
    }
}