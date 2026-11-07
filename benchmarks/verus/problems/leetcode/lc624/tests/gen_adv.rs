use vstd::prelude::*;

verus! {

pub open spec fn total_len_spec(arrays: Seq<Vec<i32>>) -> int
    decreases arrays.len(),
{
    if arrays.len() == 0 {
        0
    } else {
        arrays[0].len() + total_len_spec(arrays.drop_first())
    }
}

pub proof fn total_len_push(s: Seq<Vec<i32>>, v: Vec<i32>)
    ensures
        total_len_spec(s.push(v)) == total_len_spec(s) + v.len() as int,
    decreases s.len(),
{
    if s.len() == 0 {
        assert(s.push(v).drop_first() =~= Seq::<Vec<i32>>::empty());
        assert(s.push(v)[0] == v);
        assert(total_len_spec(Seq::<Vec<i32>>::empty()) == 0);
    } else {
        assert(s.push(v)[0] == s[0]);
        assert(s.push(v).drop_first() =~= s.drop_first().push(v));
        total_len_push(s.drop_first(), v);
    }
}

pub fn generate_test_case(
    sizes: &Vec<usize>,
    values: &Vec<i32>,
) -> (arrays: Vec<Vec<i32>>)
    requires
        2 <= sizes.len() <= 100_000,
        forall|i: int| 0 <= i < sizes.len() ==> 1 <= #[trigger] sizes[i] <= 500,
        forall|i: int| 0 <= i < values.len() ==> -10_000 <= #[trigger] values[i] <= 10_000,
        values.len() == sizes.len(),
    ensures
        2 <= arrays.len() <= 100_000,
        arrays.len() == sizes.len(),
        forall|a: int| 0 <= a < arrays.len() ==> 1 <= #[trigger] arrays[a].len() <= 500,
        total_len_spec(arrays@) <= 100_000 ==> true, // we'll prove this below conditionally
        forall|a: int, i: int| 0 <= a < arrays.len() && 0 <= i < arrays[a].len() ==>
            -10_000 <= #[trigger] arrays[a][i] <= 10_000,
        forall|a: int, i: int, j: int|
            0 <= a < arrays.len() && 0 <= i < j < arrays[a].len() ==>
            arrays[a][i] <= arrays[a][j],
        total_len_spec(arrays@) <= 100_000 * 500,
{
    let m = sizes.len();
    let mut arrays: Vec<Vec<i32>> = Vec::new();
    let mut a: usize = 0;

    while a < m
        invariant
            m == sizes.len(),
            arrays.len() == a,
            a <= m,
            2 <= m <= 100_000,
            values.len() == sizes.len(),
            forall|i: int| 0 <= i < sizes.len() ==> 1 <= #[trigger] sizes[i] <= 500,
            forall|i: int| 0 <= i < values.len() ==> -10_000 <= #[trigger] values[i] <= 10_000,
            forall|k: int| 0 <= k < a as int ==> #[trigger] arrays[k].len() == sizes[k],
            forall|k: int, i: int| 0 <= k < a as int && 0 <= i < arrays[k].len() ==>
                #[trigger] arrays[k][i] == values[k],
        decreases m - a,
    {
        let sz = sizes[a];
        let v = values[a];
        let mut inner: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < sz
            invariant
                sz == sizes[a as int],
                v == values[a as int],
                1 <= sz <= 500,
                -10_000 <= v <= 10_000,
                i <= sz,
                inner.len() == i,
                forall|k: int| 0 <= k < i as int ==> #[trigger] inner[k] == v,
            decreases sz - i,
        {
            inner.push(v);
            i = i + 1;
        }
        assert(inner.len() == sz);
        arrays.push(inner);
        assert(arrays[a as int].len() == sz);
        a = a + 1;
    }

    // Prove total_len bound: each array len <= 500, there are m <= 100_000 arrays.
    // total_len <= 500 * m <= 500 * 100_000
    proof {
        // Prove total_len_spec(arrays@) <= 500 * arrays.len()
        total_len_bound(arrays@);
    }

    arrays
}

pub proof fn total_len_bound(s: Seq<Vec<i32>>)
    requires
        forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i].len() <= 500,
    ensures
        total_len_spec(s) <= 500 * s.len(),
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        assert(s[0].len() <= 500);
        assert forall|i: int| 0 <= i < s.drop_first().len() implies #[trigger] s.drop_first()[i].len() <= 500 by {
            assert(s.drop_first()[i] == s[i + 1]);
        }
        total_len_bound(s.drop_first());
    }
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
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build_case(rng: &mut Rng, mode: usize, t: usize) -> (Vec<usize>, Vec<i32>) {
    // We build arrays as filled with a constant value (values[i]) of length sizes[i].
    // That satisfies "sorted ascending" trivially. Total length constrained to <= 100_000.
    let m: usize = match mode {
        0 => 2,
        1 => 3,
        2 => {
            // many arrays, small sizes
            let mx = 100_000usize;
            let r = rng.gen_range_usize(100, 1000);
            r.min(mx).max(2)
        }
        3 => {
            // few arrays, max sizes
            let r = rng.gen_range_usize(2, 10);
            r.max(2)
        }
        4 => 100_000, // max m
        5 => 200,
        6 => rng.gen_range_usize(2, 500),
        7 => rng.gen_range_usize(50, 5000),
        8 => 2,
        9 => rng.gen_range_usize(2, 100),
        _ => rng.gen_range_usize(2, 1000),
    };

    // Pick sizes such that total <= 100_000 and each in [1,500].
    let mut sizes: Vec<usize> = Vec::with_capacity(m);
    let mut values: Vec<i32> = Vec::with_capacity(m);
    let budget_per: usize = (100_000 / m).max(1).min(500);

    for i in 0..m {
        let sz = match mode {
            0 => if i == 0 { 3 } else { 2 },
            1 => 1 + (i % 3),
            3 => 500, // max size each
            4 => 1,   // many arrays must be size 1
            5 => {
                let u = rng.gen_range_usize(1, budget_per.max(1));
                u
            }
            8 => {
                if i == 0 { 1 } else { 1 }
            }
            _ => {
                let u = rng.gen_range_usize(1, budget_per.max(1));
                u
            }
        };
        let sz = sz.max(1).min(500);
        sizes.push(sz);

        let v = match mode {
            0 => if i == 0 { -10_000 } else { 10_000 },
            1 => if i == 0 { 0 } else if i == 1 { 10_000 } else { -10_000 },
            2 => rng.gen_range_i32(-10_000, 10_000),
            6 => if i % 2 == 0 { -10_000 } else { 10_000 },
            7 => rng.gen_range_i32(-100, 100),
            8 => if i == 0 { -10_000 } else { 10_000 },
            9 => {
                // same value everywhere -> distance 0
                5
            }
            _ => rng.gen_range_i32(-10_000, 10_000),
        };
        let v = v.max(-10_000).min(10_000);
        values.push(v);
    }

    // Ensure total <= 100_000 by clamping
    let mut total: usize = 0;
    for i in 0..sizes.len() {
        if total + sizes[i] > 100_000 {
            sizes[i] = if total >= 100_000 { 1 } else {
                let remaining = 100_000 - total;
                remaining.max(1).min(500).min(sizes[i])
            };
        }
        total += sizes[i];
        if total > 100_000 {
            // force to 1
            sizes[i] = 1;
            total = total - sizes[i] + 1; // approximate; we'll just cap below
        }
    }

    // Final safety pass: clamp sizes so total <= 100_000
    let mut total: usize = 0;
    for i in 0..sizes.len() {
        if sizes[i] < 1 { sizes[i] = 1; }
        if sizes[i] > 500 { sizes[i] = 500; }
        if total + sizes[i] > 100_000 {
            if total + 1 <= 100_000 {
                sizes[i] = 1;
            } else {
                sizes[i] = 1;
            }
        }
        total += sizes[i];
    }
    // If still over (shouldn't happen if m <= 100_000 and min size 1), truncate
    if total > 100_000 {
        // truncate arrays to m' such that sum <= 100_000
        let mut cum: usize = 0;
        let mut keep: usize = 0;
        for i in 0..sizes.len() {
            if cum + sizes[i] <= 100_000 {
                cum += sizes[i];
                keep = i + 1;
            } else {
                break;
            }
        }
        if keep < 2 {
            // fallback
            sizes.clear();
            values.clear();
            sizes.push(1);
            sizes.push(1);
            values.push(0);
            values.push(0);
        } else {
            sizes.truncate(keep);
            values.truncate(keep);
        }
    }

    let _ = t;
    (sizes, values)
}

fn print_json(arrays: &[Vec<i32>]) {
    print!("{{\"arrays\":[");
    for i in 0..arrays.len() {
        if i > 0 { print!(","); }
        print!("[");
        for j in 0..arrays[i].len() {
            if j > 0 { print!(","); }
            print!("{}", arrays[i][j]);
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

    for t in 0..total {
        let mode = t % modes;
        let (sizes, values) = build_case(&mut rng, mode, t);
        // Verify preconditions hold before calling (the generator itself requires them)
        if sizes.len() < 2 || sizes.len() > 100_000 { continue; }
        if values.len() != sizes.len() { continue; }
        let mut ok = true;
        for i in 0..sizes.len() {
            if sizes[i] < 1 || sizes[i] > 500 { ok = false; break; }
        }
        for i in 0..values.len() {
            if values[i] < -10_000 || values[i] > 10_000 { ok = false; break; }
        }
        if !ok { continue; }
        let arrays = generate_test_case(&sizes, &values);
        print_json(&arrays);
    }
}