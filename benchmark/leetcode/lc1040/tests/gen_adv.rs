use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, start: i32, gap_index: usize, extra_gap: i32) -> (stones: Vec<i32>)
    requires
        3 <= n <= 10000,
        1 <= start as int,
        gap_index < n - 1,
        1 <= extra_gap as int,
        start as int + (n as int - 1) + extra_gap as int <= 1_000_000_000,
    ensures
        stones@.len() == n as int,
        forall |i: int, j: int| 0 <= i < j < stones@.len() ==> stones@[i] != stones@[j],
        forall |i: int| 0 <= i < stones@.len() ==> 1 <= #[trigger] stones[i] <= 1_000_000_000i32,
{
    let mut stones: Vec<i32> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            3 <= n <= 10000,
            1 <= start as int,
            gap_index < n - 1,
            1 <= extra_gap as int,
            start as int + (n as int - 1) + extra_gap as int <= 1_000_000_000,
            i <= n,
            stones.len() == i,
            forall|k: int| 0 <= k < stones.len() ==> #[trigger] stones[k] as int
                == start as int + k + if k > gap_index as int { extra_gap as int } else { 0int },
            forall|k: int| 0 <= k < stones.len() ==> 1 <= #[trigger] stones[k] <= 1_000_000_000i32,
            forall|a: int, b: int| 0 <= a < b < stones.len() ==> stones[a] != stones[b],
        decreases n - i,
    {
        let v: i32 = if i <= gap_index {
            start + i as i32
        } else {
            start + i as i32 + extra_gap
        };

        assert(v as int == start as int + i as int + if i as int > gap_index as int { extra_gap as int } else { 0int });
        assert(1 <= v as int);
        if i <= gap_index {
            assert(v as int == start as int + i as int);
            assert(i as int <= n as int - 1);
            assert(v as int <= start as int + (n as int - 1));
            assert(start as int + (n as int - 1) <= start as int + (n as int - 1) + extra_gap as int);
            assert(v as int <= 1_000_000_000);
        } else {
            assert(v as int == start as int + i as int + extra_gap as int);
            assert(i as int <= n as int - 1);
            assert(v as int <= start as int + (n as int - 1) + extra_gap as int);
            assert(v as int <= 1_000_000_000);
        }

        stones.push(v);

        proof {
            assert forall|k: int| 0 <= k < stones.len() implies #[trigger] stones[k] as int
                == start as int + k + if k > gap_index as int { extra_gap as int } else { 0int } by {
                if k < i as int {
                } else {
                    assert(k == i as int);
                    assert(stones[k] == v);
                }
            };

            assert forall|k: int| 0 <= k < stones.len() implies 1 <= #[trigger] stones[k] <= 1_000_000_000i32 by {
                if k < i as int {
                } else {
                    assert(k == i as int);
                    assert(stones[k] == v);
                }
            };

            assert forall|a: int, b: int| 0 <= a < b < stones.len() implies stones[a] != stones[b] by {
                if b < i as int {
                } else {
                    assert(b == i as int);
                    assert(stones[b] == v);
                    assert(stones[a] as int == start as int + a + if a > gap_index as int { extra_gap as int } else { 0int });
                    assert(stones[b] as int == start as int + b + if b > gap_index as int { extra_gap as int } else { 0int });

                    if b <= gap_index as int {
                        assert(a <= gap_index as int);
                        assert(stones[a] as int == start as int + a);
                        assert(stones[b] as int == start as int + b);
                        assert(a < b);
                        assert(start as int + a < start as int + b);
                    } else if a > gap_index as int {
                        assert(stones[a] as int == start as int + a + extra_gap as int);
                        assert(stones[b] as int == start as int + b + extra_gap as int);
                        assert(a < b);
                        let sa = start as int + a + extra_gap as int;
                        let sb = start as int + b + extra_gap as int;
                        assert(sa < sb);
                        assert(stones[a] as int == sa);
                        assert(stones[b] as int == sb);
                    } else {
                        assert(a <= gap_index as int);
                        assert(stones[a] as int == start as int + a);
                        assert(stones[b] as int == start as int + b + extra_gap as int);
                        assert(1 <= extra_gap as int);
                        assert(a < b);
                        assert(a + 1 <= b);
                        assert(a < b + extra_gap as int);
                        assert(start as int + a < start as int + b + extra_gap as int);
                    }
                    assert(stones[a] as int != stones[b] as int);
                }
            };
        }

        i = i + 1;
    }

    stones
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

    fn gen_range_u64(&mut self, lo: u64, hi: u64) -> u64 {
        assert!(lo <= hi);
        let span = hi - lo + 1;
        lo + (self.next_u64() % span)
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        self.gen_range_u64(lo as u64, hi as u64) as usize
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn choose_case(rng: &mut Rng, mode: usize) -> (usize, i32, usize, i32) {
    match mode {
        0 => {
            let n = 3usize;
            let start = 1i32;
            let gap_index = 0usize;
            let extra_gap = 1_000_000_000i32 - start - (n as i32 - 1);
            (n, start, gap_index, extra_gap)
        }
        1 => {
            let n = 10000usize;
            let start = 1i32;
            let gap_index = n - 2;
            let extra_gap = 1i32;
            (n, start, gap_index, extra_gap)
        }
        2 => {
            let n = 10000usize;
            let start = 1i32;
            let gap_index = 0usize;
            let extra_gap = 1i32;
            (n, start, gap_index, extra_gap)
        }
        3 => {
            let n = 9999usize;
            let start = 12345i32;
            let gap_index = n / 2;
            let extra_gap = 1i32;
            (n, start, gap_index, extra_gap)
        }
        4 => {
            let n = 8usize;
            let start = 50i32;
            let gap_index = 3usize;
            let extra_gap = 25i32;
            (n, start, gap_index, extra_gap)
        }
        5 => {
            let n = 5usize;
            let start = 999_999_990i32;
            let gap_index = 1usize;
            let extra_gap = 4i32;
            (n, start, gap_index, extra_gap)
        }
        6 => {
            let n = 6usize;
            let start = 1i32;
            let gap_index = 4usize;
            let extra_gap = 100i32;
            (n, start, gap_index, extra_gap)
        }
        7 => {
            let n = 7usize;
            let start = 100i32;
            let gap_index = 0usize;
            let extra_gap = 5000i32;
            (n, start, gap_index, extra_gap)
        }
        8 => {
            let n = 4usize;
            let start = 7i32;
            let gap_index = 1usize;
            let extra_gap = 2i32;
            (n, start, gap_index, extra_gap)
        }
        9 => {
            let n = 3usize + rng.gen_range_usize(0, 9997);
            let max_start = 1_000_000_000i32 - ((n - 1) as i32) - 1;
            let start = rng.gen_range_i32(1, max_start.max(1));
            let gap_index = rng.gen_range_usize(0, n - 2);
            let max_extra = 1_000_000_000i32 - start - ((n - 1) as i32);
            let extra_gap = rng.gen_range_i32(1, max_extra.max(1));
            (n, start, gap_index, extra_gap)
        }
        _ => {
            let n = 3usize + rng.gen_range_usize(0, 200);
            let max_start = 1_000_000_000i32 - ((n - 1) as i32) - 1000;
            let start = rng.gen_range_i32(1, max_start.max(1));
            let gap_index = rng.gen_range_usize(0, n - 2);
            let max_extra = (1_000_000_000i32 - start - ((n - 1) as i32)).min(1000).max(1);
            let extra_gap = rng.gen_range_i32(1, max_extra);
            (n, start, gap_index, extra_gap)
        }
    }
}

fn print_json_line(stones: &[i32]) {
    use std::io::Write;
    let stdout = std::io::stdout();
    let mut out = std::io::BufWriter::new(stdout.lock());
    write!(out, "{{\"stones\":[").unwrap();
    for (i, v) in stones.iter().enumerate() {
        if i > 0 {
            write!(out, ",").unwrap();
        }
        write!(out, "{}", v).unwrap();
    }
    writeln!(out, "]}}").unwrap();
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let total = 200usize;

    for t in 0..total {
        let mode = if t < 100 { t % 10 } else { 10 };
        let (n, start, gap_index, extra_gap) = choose_case(&mut rng, mode);
        let stones = generate_test_case(n, start, gap_index, extra_gap);
        print_json_line(&stones);
    }
}