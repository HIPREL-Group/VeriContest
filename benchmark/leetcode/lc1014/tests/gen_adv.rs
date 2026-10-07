use vstd::prelude::*;

verus! {

pub open spec fn filler_index(k: int, idx_hi: int, idx_lo: int) -> int {
    k - (if idx_hi < k { 1int } else { 0int })
      - (if idx_lo < k { 1int } else { 0int })
}

pub fn generate_test_case(
    high_val: i32,
    low_val: i32,
    idx_hi: usize,
    idx_lo: usize,
    fillers: &Vec<i32>,
) -> (values: Vec<i32>)
    requires
        1 <= low_val <= high_val <= 1000,
        idx_hi < idx_lo,
        idx_lo < fillers.len() + 2,
        fillers.len() + 2 <= 50_000,
        forall|i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 1000,
    ensures
        2 <= values.len() <= 50_000,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1000,
{
    let n: usize = fillers.len() + 2;
    assert(2 <= n);
    assert(idx_hi < idx_lo);
    assert(idx_lo < n);
    assert(idx_hi < n);

    let mut values: Vec<i32> = Vec::new();
    let mut fi: usize = 0;
    let mut pos: usize = 0;

    while pos < n
        invariant
            n == fillers.len() + 2,
            2 <= n <= 50_000,
            idx_hi < idx_lo,
            idx_lo < n,
            idx_hi < n,
            0 <= pos <= n,
            values.len() == pos,
            0 <= fi <= fillers.len(),
            fi == pos - (if idx_hi < pos { 1usize } else { 0usize })
                      - (if idx_lo < pos { 1usize } else { 0usize }),
            1 <= low_val <= high_val <= 1000,
            forall|i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 1000,
            forall|k: int| 0 <= k < pos as int && k == idx_hi as int ==> #[trigger] values[k] == high_val,
            forall|k: int| 0 <= k < pos as int && k == idx_lo as int ==> #[trigger] values[k] == low_val,
            forall|k: int| 0 <= k < pos as int && k != idx_hi as int && k != idx_lo as int ==>
                #[trigger] values[k] == fillers[filler_index(k, idx_hi as int, idx_lo as int)],
            forall|k: int| 0 <= k < pos as int ==> 1 <= #[trigger] values[k] <= 1000,
        decreases n - pos,
    {
        if pos == idx_hi {
            values.push(high_val);
        } else if pos == idx_lo {
            values.push(low_val);
        } else {
            assert(fi < fillers.len());
            assert(fi as int == filler_index(pos as int, idx_hi as int, idx_lo as int));
            values.push(fillers[fi]);
            fi = fi + 1;
        }
        pos = pos + 1;
    }

    values
}

} // verus!

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        Self(seed)
    }

    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        let range = hi - lo + 1;
        lo + (self.next_u64() as usize % range)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let range = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % range) as i32
    }
}

fn make_fillers(rng: &mut Rng, count: usize, mode: usize, hi: i32, lo: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(count);
    let mut i = 0usize;
    while i < count {
        let x = match mode % 10 {
            0 => 1,
            1 => 1000,
            2 => {
                if i % 2 == 0 { 1 } else { 1000 }
            }
            3 => {
                let t = 1000i32.saturating_sub(i as i32);
                if t < 1 { 1 } else { t }
            }
            4 => {
                let t = 1 + (i % 1000) as i32;
                if t > 1000 { 1000 } else { t }
            }
            5 => hi,
            6 => lo,
            7 => {
                let d = (i % 7) as i32;
                let t = hi - d;
                if t < 1 { 1 } else { t }
            }
            8 => {
                let d = (i % 7) as i32;
                let t = lo + d;
                if t > 1000 { 1000 } else { t }
            }
            _ => rng.gen_range_i32(1, 1000),
        };
        v.push(x);
        i += 1;
    }
    v
}

fn print_json_array(values: &[i32]) {
    use std::io::Write;
    let stdout = std::io::stdout();
    let mut out = std::io::BufWriter::new(stdout.lock());
    write!(out, "{{\"values\":[").unwrap();
    let mut i = 0usize;
    while i < values.len() {
        if i > 0 {
            write!(out, ",").unwrap();
        }
        write!(out, "{}", values[i]).unwrap();
        i += 1;
    }
    writeln!(out, "]}}").unwrap();
}

fn build_case(rng: &mut Rng, case_id: usize) -> Vec<i32> {
    let mode = case_id % 10;
    let n = match mode {
        0 => 2,
        1 => 3,
        2 => 5,
        3 => 10,
        4 => 50,
        5 => 200,
        6 => 1000,
        7 => 5000,
        8 => 20000,
        _ => 50000,
    };

    let (idx_hi, idx_lo) = match mode {
        0 => (0usize, n - 1),
        1 => (0usize, 1usize),
        2 => (n - 2, n - 1),
        3 => (0usize, n / 2),
        4 => (n / 3, n / 3 + 1),
        5 => (1usize, n - 1),
        6 => (0usize, n - 2),
        7 => (n / 2 - 1, n / 2),
        8 => {
            let i = rng.gen_range_usize(0, n - 2);
            let j = rng.gen_range_usize(i + 1, n - 1);
            (i, j)
        }
        _ => {
            let i = rng.gen_range_usize(0, n - 2);
            let j = rng.gen_range_usize(i + 1, n - 1);
            (i, j)
        }
    };

    let (hi, lo) = match mode {
        0 => (1000, 1000),
        1 => (1000, 1),
        2 => (1, 1),
        3 => (999, 998),
        4 => (500, 500),
        5 => (1000, 999),
        6 => (2, 1),
        7 => (rng.gen_range_i32(900, 1000), rng.gen_range_i32(1, 100)),
        8 => {
            let h = rng.gen_range_i32(1, 1000);
            let l = rng.gen_range_i32(1, h);
            (h, l)
        }
        _ => {
            let h = rng.gen_range_i32(1, 1000);
            let l = rng.gen_range_i32(1, h);
            (h, l)
        }
    };

    let fillers = make_fillers(rng, n - 2, mode, hi, lo);
    generate_test_case(hi, lo, idx_hi, idx_lo, &fillers)
}

fn main() {
    let seed = std::env::args()
        .nth(1)
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(1);

    let mut rng = Rng::new(seed);
    let total = 200usize;
    let mut i = 0usize;
    while i < total {
        let values = build_case(&mut rng, i);
        print_json_array(&values);
        i += 1;
    }
}