use vstd::prelude::*;

verus! {

pub struct Gen;

spec fn filler_pos_to_index(pos: int, special_idx: int) -> int {
    pos - if special_idx < pos { 1int } else { 0int }
}

pub fn generate_test_case(
    len: usize,
    special_idx: usize,
    special_val: i32,
    fillers: &Vec<i32>,
) -> (piles: Vec<i32>)
    requires
        1 <= len <= 100,
        special_idx < len,
        fillers.len() + 1 == len,
        1 <= special_val <= 10000,
        forall|i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 10000,
    ensures
        1 <= piles.len() <= 100,
        forall|i: int| 0 <= i < piles.len() ==> 1 <= #[trigger] piles[i] <= 10000,
{
    let mut piles: Vec<i32> = Vec::new();
    let mut pos: usize = 0;
    let mut fi: usize = 0;

    while pos < len
        invariant
            1 <= len <= 100,
            special_idx < len,
            fillers.len() + 1 == len,
            1 <= special_val <= 10000,
            forall|i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 10000,
            0 <= pos <= len,
            piles.len() == pos,
            0 <= fi <= fillers.len(),
            fi == pos - (if special_idx < pos { 1usize } else { 0usize }),
            forall|k: int| 0 <= k < pos as int && k == special_idx as int ==> #[trigger] piles[k] == special_val,
            forall|k: int| 0 <= k < pos as int && k != special_idx as int ==>
                #[trigger] piles[k] == fillers[filler_pos_to_index(k, special_idx as int)],
            forall|k: int| 0 <= k < pos as int ==> 1 <= #[trigger] piles[k] <= 10000,
        decreases len - pos,
    {
        if pos == special_idx {
            piles.push(special_val);
        } else {
            assert(fi < fillers.len());
            assert(fi as int == filler_pos_to_index(pos as int, special_idx as int));
            piles.push(fillers[fi]);
            fi = fi + 1;
        }
        pos = pos + 1;
    }

    assert(piles.len() == len);
    piles
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

fn make_fillers(len: usize, mode: usize, rng: &mut Rng) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    match mode {
        0 => {
            for _ in 0..len {
                v.push(1);
            }
        }
        1 => {
            for _ in 0..len {
                v.push(10_000);
            }
        }
        2 => {
            for i in 0..len {
                v.push(if i % 2 == 0 { 1 } else { 10_000 });
            }
        }
        3 => {
            for i in 0..len {
                let x = (i % 97) as i32 + 1;
                v.push(x);
            }
        }
        4 => {
            for i in 0..len {
                let x = 10_000 - (i % 97) as i32;
                v.push(x);
            }
        }
        5 => {
            for i in 0..len {
                v.push(if i < len / 2 { 1 } else { 10_000 });
            }
        }
        6 => {
            for i in 0..len {
                let x = ((i * i + 17 * i + 23) % 10_000) as i32 + 1;
                v.push(x);
            }
        }
        7 => {
            for _ in 0..len {
                v.push(rng.gen_range_i32(1, 10_000));
            }
        }
        8 => {
            for i in 0..len {
                v.push(if i % 3 == 0 { 2 } else if i % 3 == 1 { 3 } else { 4 });
            }
        }
        9 => {
            for i in 0..len {
                v.push(if i + 1 == len { 10_000 } else { 1 });
            }
        }
        _ => {
            for i in 0..len {
                let x = (((i * 37) ^ (i * 91 + 7)) % 10_000) as i32 + 1;
                v.push(x);
            }
        }
    }
    v
}

fn print_json_line(piles: &[i32]) {
    print!("{{\"piles\":[");
    for i in 0..piles.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", piles[i]);
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
    let total = 220usize;
    let modes = 11usize;

    for t in 0..total {
        let mode = t % modes;
        let len = match mode {
            0 => 1,
            1 => 100,
            2 => 2,
            3 => 99,
            4 => 50,
            5 => 3 + (t % 10),
            6 => 17,
            7 => 64,
            8 => 37,
            9 => 75,
            _ => rng.gen_range_usize(1, 100),
        };

        let special_idx = match mode {
            0 => 0,
            1 => 99,
            2 => 1,
            3 => 0,
            4 => len / 2,
            5 => len - 1,
            6 => 1,
            7 => len / 3,
            8 => len - 1,
            9 => 0,
            _ => rng.gen_range_usize(0, len - 1),
        };

        let special_val = match mode {
            0 => 1,
            1 => 10_000,
            2 => 10_000,
            3 => 1,
            4 => 5000,
            5 => 9999,
            6 => 2,
            7 => 7777,
            8 => 3,
            9 => 10_000,
            _ => rng.gen_range_i32(1, 10_000),
        };

        let fillers = make_fillers(len - 1, mode, &mut rng);
        let piles = generate_test_case(len, special_idx, special_val, &fillers);
        print_json_line(&piles);
    }
}