use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    m: i32,
    n: i32,
    rs: &Vec<i32>,
    cs: &Vec<i32>,
) -> (result: (i32, i32, Vec<Vec<i32>>))
    requires
        1 <= m <= 50,
        1 <= n <= 50,
        rs.len() == cs.len(),
        1 <= rs.len() <= 100,
        forall|k: int| 0 <= k < rs.len() ==> 0 <= #[trigger] rs[k] < m,
        forall|k: int| 0 <= k < cs.len() ==> 0 <= #[trigger] cs[k] < n,
    ensures
        ({
            let (rm, rn, indices) = result;
            &&& rm == m
            &&& rn == n
            &&& 1 <= rm <= 50
            &&& 1 <= rn <= 50
            &&& 1 <= indices.len() <= 100
            &&& forall|k: int| 0 <= k < indices.len() ==>
                    (#[trigger] indices.deep_view()[k]).len() == 2
            &&& forall|k: int| 0 <= k < indices.len() ==>
                    0 <= (#[trigger] indices.deep_view()[k])[0] < rm
            &&& forall|k: int| 0 <= k < indices.len() ==>
                    0 <= (#[trigger] indices.deep_view()[k])[1] < rn
        }),
{
    let len = rs.len();
    let mut indices: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;

    while i < len
        invariant
            len == rs.len(),
            len == cs.len(),
            1 <= len <= 100,
            0 <= i <= len,
            indices.len() == i,
            1 <= m <= 50,
            1 <= n <= 50,
            forall|k: int| 0 <= k < rs.len() ==> 0 <= #[trigger] rs[k] < m,
            forall|k: int| 0 <= k < cs.len() ==> 0 <= #[trigger] cs[k] < n,
            forall|k: int| 0 <= k < i as int ==>
                (#[trigger] indices.deep_view()[k]).len() == 2,
            forall|k: int| 0 <= k < i as int ==>
                (#[trigger] indices.deep_view()[k])[0] == rs[k],
            forall|k: int| 0 <= k < i as int ==>
                (#[trigger] indices.deep_view()[k])[1] == cs[k],
        decreases len - i,
    {
        let mut pair: Vec<i32> = Vec::new();
        pair.push(rs[i]);
        pair.push(cs[i]);
        assert(pair.deep_view().len() == 2);
        assert(pair.deep_view()[0] == rs[i as int]);
        assert(pair.deep_view()[1] == cs[i as int]);

        let ghost old_indices = indices.deep_view();
        indices.push(pair);

        assert(indices.deep_view().len() == i + 1);
        assert forall|k: int| 0 <= k < (i + 1) as int implies
            (#[trigger] indices.deep_view()[k]).len() == 2
            && indices.deep_view()[k][0] == rs[k]
            && indices.deep_view()[k][1] == cs[k]
        by {
            if k < i as int {
                assert(indices.deep_view()[k] == old_indices[k]);
            } else {
                assert(k == i as int);
            }
        }

        i = i + 1;
    }

    (m, n, indices)
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

fn make_test(rng: &mut Rng, mode: usize, t: usize) -> (i32, i32, Vec<i32>, Vec<i32>) {
    let (m, n, len): (i32, i32, usize) = match mode {
        0 => (1, 1, 1),
        1 => (1, 1, 100),
        2 => (50, 50, 100),
        3 => (50, 50, 1),
        4 => (1, 50, rng.gen_range_usize(1, 100)),
        5 => (50, 1, rng.gen_range_usize(1, 100)),
        6 => {
            let m = rng.gen_range_i32(1, 50);
            let n = rng.gen_range_i32(1, 50);
            (m, n, rng.gen_range_usize(1, 100))
        }
        7 => (2, 2, 100),
        8 => (3, 3, 100),
        9 => {
            let m = rng.gen_range_i32(1, 50);
            let n = rng.gen_range_i32(1, 50);
            (m, n, 1)
        }
        _ => {
            let m = rng.gen_range_i32(1, 50);
            let n = rng.gen_range_i32(1, 50);
            (m, n, rng.gen_range_usize(1, 100))
        }
    };

    let _ = t;
    let mut rs: Vec<i32> = Vec::with_capacity(len);
    let mut cs: Vec<i32> = Vec::with_capacity(len);

    for i in 0..len {
        let r = match mode {
            7 | 8 => {
                if i % 2 == 0 { 0 } else { m - 1 }
            }
            _ => rng.gen_range_i32(0, m - 1),
        };
        let c = match mode {
            7 | 8 => {
                if i % 2 == 0 { 0 } else { n - 1 }
            }
            _ => rng.gen_range_i32(0, n - 1),
        };
        rs.push(r);
        cs.push(c);
    }
    (m, n, rs, cs)
}

fn print_json(m: i32, n: i32, indices: &Vec<Vec<i32>>) {
    print!("{{\"m\":{},\"n\":{},\"indices\":[", m, n);
    for i in 0..indices.len() {
        if i > 0 {
            print!(",");
        }
        print!("[{},{}]", indices[i][0], indices[i][1]);
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
    let modes = 11usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (m, n, rs, cs) = make_test(&mut rng, mode, t);
        let (rm, rn, indices) = generate_test_case(m, n, &rs, &cs);
        print_json(rm, rn, &indices);
    }
}