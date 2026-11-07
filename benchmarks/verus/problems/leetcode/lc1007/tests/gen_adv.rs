use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    tops_fillers: &Vec<i32>,
    bottoms_fillers: &Vec<i32>,
    first_top: i32,
    first_bottom: i32,
) -> (result: (Vec<i32>, Vec<i32>, i32))
    requires
        1 <= first_top <= 6,
        1 <= first_bottom <= 6,
        1 <= tops_fillers.len(),
        2 <= tops_fillers.len() + 1 <= 20000,
        bottoms_fillers.len() == tops_fillers.len(),
        forall|i: int| 0 <= i < tops_fillers.len() ==> 1 <= #[trigger] tops_fillers[i] <= 6,
        forall|i: int| 0 <= i < bottoms_fillers.len() ==> 1 <= #[trigger] bottoms_fillers[i] <= 6,
    ensures
        result.0.len() == tops_fillers.len() + 1,
        result.1.len() == bottoms_fillers.len() + 1,
        2 <= result.0.len() <= 20000,
        result.1.len() == result.0.len(),
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 6,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 6,
        1 <= result.2 <= 6,
{
    let n: usize = tops_fillers.len() + 1;
    let mut tops: Vec<i32> = Vec::new();
    let mut bottoms: Vec<i32> = Vec::new();

    tops.push(first_top);
    bottoms.push(first_bottom);

    let mut i: usize = 0;
    while i < tops_fillers.len()
        invariant
            n == tops_fillers.len() + 1,
            bottoms_fillers.len() == tops_fillers.len(),
            1 <= first_top <= 6,
            1 <= first_bottom <= 6,
            1 <= n <= 20000,
            0 <= i <= tops_fillers.len(),
            tops.len() == i + 1,
            bottoms.len() == i + 1,
            tops[0] == first_top,
            bottoms[0] == first_bottom,
            forall|k: int| 0 <= k < tops_fillers.len() ==> 1 <= #[trigger] tops_fillers[k] <= 6,
            forall|k: int| 0 <= k < bottoms_fillers.len() ==> 1 <= #[trigger] bottoms_fillers[k] <= 6,
            forall|k: int| 0 <= k < tops.len() ==> 1 <= #[trigger] tops[k] <= 6,
            forall|k: int| 0 <= k < bottoms.len() ==> 1 <= #[trigger] bottoms[k] <= 6,
            forall|k: int| 1 <= k < tops.len() ==> #[trigger] tops[k] == tops_fillers[k - 1],
            forall|k: int| 1 <= k < bottoms.len() ==> #[trigger] bottoms[k] == bottoms_fillers[k - 1],
        decreases tops_fillers.len() - i,
    {
        assert(i < tops_fillers.len());
        assert(i < bottoms_fillers.len());
        assert(1 <= tops_fillers[i as int] <= 6);
        assert(1 <= bottoms_fillers[i as int] <= 6);
        tops.push(tops_fillers[i]);
        bottoms.push(bottoms_fillers[i]);
        i = i + 1;
    }

    assert(tops.len() == tops_fillers.len() + 1);
    assert(bottoms.len() == bottoms_fillers.len() + 1);
    assert(bottoms.len() == tops.len());
    assert(1 <= tops.len() <= 20000);

    (tops, bottoms, first_top)
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

    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize % (hi - lo + 1))
    }

    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        lo + (self.next_u64() % ((hi - lo + 1) as u64)) as i32
    }

    fn gen_bool(&mut self) -> bool {
        (self.next_u64() & 1) == 1
    }
}

fn choose_not(rng: &mut Rng, banned: i32) -> i32 {
    loop {
        let x = rng.gen_i32(1, 6);
        if x != banned {
            return x;
        }
    }
}

fn choose_pair_without(rng: &mut Rng, banned: i32) -> (i32, i32) {
    let a = choose_not(rng, banned);
    let b = choose_not(rng, banned);
    (a, b)
}

fn make_case(mode: usize, rng: &mut Rng) -> (Vec<i32>, Vec<i32>, i32) {
    let n = match mode {
        0 => 2,
        1 => 3,
        2 => 4,
        3 => 5,
        4 => 6,
        5 => 7,
        6 => 17,
        7 => 64,
        8 => 511,
        _ => rng.gen_usize(2, 20000),
    };

    let v = rng.gen_i32(1, 6);
    let mut tops_fillers = Vec::with_capacity(n - 1);
    let mut bottoms_fillers = Vec::with_capacity(n - 1);

    match mode {
        0 => {
            for _ in 1..n {
                tops_fillers.push(v);
                bottoms_fillers.push(v);
            }
            generate_test_case(&tops_fillers, &bottoms_fillers, v, v)
        }
        1 => {
            for _ in 1..n {
                tops_fillers.push(v);
                bottoms_fillers.push(choose_not(rng, v));
            }
            generate_test_case(&tops_fillers, &bottoms_fillers, v, choose_not(rng, v))
        }
        2 => {
            for _ in 1..n {
                tops_fillers.push(choose_not(rng, v));
                bottoms_fillers.push(v);
            }
            generate_test_case(&tops_fillers, &bottoms_fillers, choose_not(rng, v), v)
        }
        3 => {
            for i in 1..n {
                if i % 2 == 0 {
                    tops_fillers.push(v);
                    bottoms_fillers.push(choose_not(rng, v));
                } else {
                    tops_fillers.push(choose_not(rng, v));
                    bottoms_fillers.push(v);
                }
            }
            generate_test_case(&tops_fillers, &bottoms_fillers, v, v)
        }
        4 => {
            for _ in 1..n {
                let a = choose_not(rng, v);
                tops_fillers.push(a);
                bottoms_fillers.push(a);
            }
            generate_test_case(&tops_fillers, &bottoms_fillers, v, v)
        }
        5 => {
            for i in 1..n {
                if i == n / 2 {
                    tops_fillers.push(v);
                    bottoms_fillers.push(v);
                } else if rng.gen_bool() {
                    tops_fillers.push(v);
                    bottoms_fillers.push(choose_not(rng, v));
                } else {
                    tops_fillers.push(choose_not(rng, v));
                    bottoms_fillers.push(v);
                }
            }
            generate_test_case(&tops_fillers, &bottoms_fillers, choose_not(rng, v), v)
        }
        6 => {
            for i in 1..n {
                if i % 3 == 0 {
                    tops_fillers.push(v);
                    bottoms_fillers.push(v);
                } else if i % 3 == 1 {
                    tops_fillers.push(v);
                    bottoms_fillers.push(choose_not(rng, v));
                } else {
                    tops_fillers.push(choose_not(rng, v));
                    bottoms_fillers.push(v);
                }
            }
            generate_test_case(&tops_fillers, &bottoms_fillers, v, choose_not(rng, v))
        }
        7 => {
            for i in 1..n {
                let x = if i % 2 == 0 { 1 } else { 6 };
                let y = if x == v { choose_not(rng, v) } else { x };
                if rng.gen_bool() {
                    tops_fillers.push(v);
                    bottoms_fillers.push(y);
                } else {
                    tops_fillers.push(y);
                    bottoms_fillers.push(v);
                }
            }
            generate_test_case(&tops_fillers, &bottoms_fillers, v, v)
        }
        8 => {
            for i in 1..n {
                if i == 1 {
                    tops_fillers.push(v);
                    bottoms_fillers.push(choose_not(rng, v));
                } else if i + 1 == n {
                    tops_fillers.push(choose_not(rng, v));
                    bottoms_fillers.push(v);
                } else {
                    let (a, b) = choose_pair_without(rng, v);
                    if rng.gen_bool() {
                        tops_fillers.push(v);
                        bottoms_fillers.push(a);
                    } else {
                        tops_fillers.push(b);
                        bottoms_fillers.push(v);
                    }
                }
            }
            generate_test_case(&tops_fillers, &bottoms_fillers, choose_not(rng, v), v)
        }
        _ => {
            for _ in 1..n {
                let style = rng.gen_usize(0, 3);
                match style {
                    0 => {
                        tops_fillers.push(v);
                        bottoms_fillers.push(choose_not(rng, v));
                    }
                    1 => {
                        tops_fillers.push(choose_not(rng, v));
                        bottoms_fillers.push(v);
                    }
                    2 => {
                        tops_fillers.push(v);
                        bottoms_fillers.push(v);
                    }
                    _ => {
                        let (a, b) = choose_pair_without(rng, v);
                        if rng.gen_bool() {
                            tops_fillers.push(a);
                            bottoms_fillers.push(v);
                        } else {
                            tops_fillers.push(v);
                            bottoms_fillers.push(b);
                        }
                    }
                }
            }
            let first_bottom = if rng.gen_bool() { v } else { choose_not(rng, v) };
            generate_test_case(&tops_fillers, &bottoms_fillers, v, first_bottom)
        }
    }
}

fn print_vec(buf: &mut String, v: &[i32]) {
    buf.push('[');
    for (i, x) in v.iter().enumerate() {
        if i > 0 {
            buf.push(',');
        }
        buf.push_str(&x.to_string());
    }
    buf.push(']');
}

fn main() {
    use std::env;
    use std::io::{self, Write};

    let seed = env::args()
        .nth(1)
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(1);

    let mut rng = Rng::new(seed);
    let stdout = io::stdout();
    let mut out = io::BufWriter::new(stdout.lock());

    for i in 0..200usize {
        let mode = if i < 100 { i % 10 } else { rng.gen_usize(0, 9) };
        let (tops, bottoms, v) = make_case(mode, &mut rng);

        let mut line = String::new();
        line.push_str("{\"tops\":");
        print_vec(&mut line, &tops);
        line.push_str(",\"bottoms\":");
        print_vec(&mut line, &bottoms);
        line.push_str(",\"v\":");
        line.push_str(&v.to_string());
        line.push('}');

        writeln!(out, "{}", line).unwrap();
    }
}