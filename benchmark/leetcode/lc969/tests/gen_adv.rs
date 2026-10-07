use vstd::prelude::*;

verus! {

pub open spec fn value_in_spec(s: Seq<i32>, v: i32) -> bool {
    exists |j: int| 0 <= j < s.len() && s[j] == v
}

pub fn generate_test_case(perm: &Vec<i32>) -> (arr: Vec<i32>)
    requires
        1 <= perm.len() <= 100,
        forall |i: int| 0 <= i < perm.len() ==>
            1 <= #[trigger] perm[i] <= perm.len() as i32,
        forall |i: int, j: int|
            0 <= i < j < perm.len() ==> perm[i] != perm[j],
        forall |v: i32| 1 <= v <= perm.len() as i32 ==>
            #[trigger] value_in_spec(perm@, v),
    ensures
        1 <= arr.len() <= 100,
        arr.len() == perm.len(),
        forall |i: int| 0 <= i < arr.len() ==>
            1 <= #[trigger] arr[i] <= arr.len() as i32,
        forall |i: int, j: int|
            0 <= i < j < arr.len() ==> arr[i] != arr[j],
        forall |v: i32| 1 <= v <= arr.len() as i32 ==>
            #[trigger] value_in_spec(arr@, v),
{
    let n = perm.len();
    let mut arr: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            n == perm.len(),
            arr.len() == k,
            forall |i: int| 0 <= i < k as int ==> #[trigger] arr[i] == perm[i],
            forall |i: int| 0 <= i < perm.len() ==>
                1 <= #[trigger] perm[i] <= perm.len() as i32,
        decreases n - k,
    {
        arr.push(perm[k]);
        k += 1;
    }

    proof {
        assert(arr@ =~= perm@);
    }

    arr
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
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
}

fn make_perm(n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    for i in 0..n {
        v.push((i + 1) as i32);
    }
    v
}

fn shuffle(rng: &mut Rng, v: &mut Vec<i32>) {
    let n = v.len();
    if n < 2 { return; }
    let mut i = n - 1;
    while i > 0 {
        let j = rng.gen_range_usize(0, i);
        v.swap(i, j);
        i -= 1;
    }
}

fn reverse_vec(v: &mut Vec<i32>) {
    let n = v.len();
    let mut i = 0;
    while i < n / 2 {
        v.swap(i, n - 1 - i);
        i += 1;
    }
}

fn adversarial(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    let n_choices = [1usize, 2, 3, 5, 10, 50, 99, 100];
    let n = n_choices[t % n_choices.len()];

    match mode {
        0 => {
            // sorted ascending
            make_perm(n)
        }
        1 => {
            // reverse sorted
            let mut v = make_perm(n);
            reverse_vec(&mut v);
            v
        }
        2 => {
            // shuffled
            let mut v = make_perm(n);
            shuffle(rng, &mut v);
            v
        }
        3 => {
            // almost sorted - one swap
            let mut v = make_perm(n);
            if n >= 2 {
                let i = rng.gen_range_usize(0, n - 1);
                let mut j = rng.gen_range_usize(0, n - 2);
                if j >= i { j += 1; }
                v.swap(i, j);
            }
            v
        }
        4 => {
            // max swapped with min
            let mut v = make_perm(n);
            if n >= 2 {
                v.swap(0, n - 1);
            }
            v
        }
        5 => {
            // rotated by 1
            let mut v = make_perm(n);
            if n >= 2 {
                let first = v[0];
                for i in 0..(n - 1) {
                    v[i] = v[i + 1];
                }
                v[n - 1] = first;
            }
            v
        }
        6 => {
            // rotated by n/2
            let mut v = make_perm(n);
            let k = n / 2;
            let mut tmp: Vec<i32> = Vec::new();
            for i in 0..n {
                tmp.push(v[(i + k) % n]);
            }
            for i in 0..n {
                v[i] = tmp[i];
            }
            v
        }
        7 => {
            // odd-even pattern
            let mut v: Vec<i32> = Vec::with_capacity(n);
            let mut i = 2;
            while i <= n as i32 {
                v.push(i);
                i += 2;
            }
            i = 1;
            while i <= n as i32 {
                v.push(i);
                i += 2;
            }
            v
        }
        8 => {
            // zigzag: 1,n,2,n-1,...
            let mut v: Vec<i32> = Vec::new();
            let mut lo = 1i32;
            let mut hi = n as i32;
            let mut take_lo = true;
            while lo <= hi {
                if take_lo {
                    v.push(lo);
                    lo += 1;
                } else {
                    v.push(hi);
                    hi -= 1;
                }
                take_lo = !take_lo;
            }
            v
        }
        _ => {
            // random perm
            let mut v = make_perm(n);
            shuffle(rng, &mut v);
            v
        }
    }
}

fn print_json(arr: &[i32]) {
    print!("{{\"arr\":[");
    for i in 0..arr.len() {
        if i > 0 { print!(","); }
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
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let perm = adversarial(&mut rng, mode, t);
        // safety guard (should always hold)
        if perm.len() < 1 || perm.len() > 100 {
            continue;
        }
        // verify properties before calling
        let n = perm.len();
        let mut ok = true;
        for i in 0..n {
            if perm[i] < 1 || perm[i] > n as i32 { ok = false; break; }
        }
        if !ok { continue; }
        // check uniqueness
        let mut seen = vec![false; n + 1];
        for i in 0..n {
            let v = perm[i] as usize;
            if seen[v] { ok = false; break; }
            seen[v] = true;
        }
        if !ok { continue; }
        let arr = generate_test_case(&perm);
        print_json(&arr);
    }
}