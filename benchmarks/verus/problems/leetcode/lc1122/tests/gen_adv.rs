use vstd::prelude::*;

verus! {

pub open spec fn count(s: Seq<i32>, v: i32) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        (if s[0] == v { 1int } else { 0int }) + count(s.subrange(1, s.len() as int), v)
    }
}

pub open spec fn no_dups(s: Seq<i32>) -> bool {
    forall |i: int, j: int| 0 <= i < j < s.len() ==> s[i] != s[j]
}

pub fn generate_test_case(arr1: Vec<i32>, arr2: Vec<i32>) -> (out: (Vec<i32>, Vec<i32>))
    requires
        1 <= arr1@.len() <= 1000,
        1 <= arr2@.len() <= 1000,
        forall |i: int| 0 <= i < arr1@.len() ==> 0 <= #[trigger] arr1@[i] <= 1000,
        forall |i: int| 0 <= i < arr2@.len() ==> 0 <= #[trigger] arr2@[i] <= 1000,
        no_dups(arr2@),
        forall |i: int| 0 <= i < arr2@.len() ==> count(arr1@, #[trigger] arr2@[i]) >= 1,
    ensures
        out.0@.len() == arr1@.len(),
        out.1@.len() == arr2@.len(),
        forall |i: int| 0 <= i < out.0@.len() ==> 0 <= #[trigger] out.0@[i] <= 1000,
        forall |i: int| 0 <= i < out.1@.len() ==> 0 <= #[trigger] out.1@[i] <= 1000,
        no_dups(out.1@),
        forall |i: int| 0 <= i < out.1@.len() ==> count(out.0@, #[trigger] out.1@[i]) >= 1,
{
    (arr1, arr2)
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

    fn shuffle<T>(&mut self, a: &mut [T]) {
        let mut i = a.len();
        while i > 1 {
            i -= 1;
            let j = self.gen_range_usize(0, i);
            a.swap(i, j);
        }
    }
}

fn contains(v: &[i32], x: i32) -> bool {
    let mut i = 0usize;
    while i < v.len() {
        if v[i] == x {
            return true;
        }
        i += 1;
    }
    false
}

fn sorted_unique_from_arr1(arr1: &[i32]) -> Vec<i32> {
    let mut seen = [false; 1001];
    let mut vals = Vec::new();
    let mut i = 0usize;
    while i < arr1.len() {
        let x = arr1[i] as usize;
        if !seen[x] {
            seen[x] = true;
            vals.push(arr1[i]);
        }
        i += 1;
    }
    vals.sort();
    vals
}

fn build_arr2_from_subset(subset: &[i32], mode: usize, rng: &mut Rng) -> Vec<i32> {
    let mut arr2 = subset.to_vec();
    match mode {
        0 => {}
        1 => arr2.reverse(),
        2 => rng.shuffle(&mut arr2),
        3 => {
            arr2.sort();
        }
        4 => {
            arr2.sort_by(|a, b| b.cmp(a));
        }
        _ => {
            rng.shuffle(&mut arr2);
        }
    }
    arr2
}

fn gen_case_mode(rng: &mut Rng, mode: usize) -> (Vec<i32>, Vec<i32>) {
    match mode {
        0 => {
            let arr1 = vec![0];
            let arr2 = vec![0];
            (arr1, arr2)
        }
        1 => {
            let arr1 = vec![2, 3, 1, 3, 2, 4, 6, 7, 9, 2, 19];
            let arr2 = vec![2, 1, 4, 3, 9, 6];
            (arr1, arr2)
        }
        2 => {
            let arr1 = vec![28, 6, 22, 8, 44, 17];
            let arr2 = vec![22, 28, 8, 6];
            (arr1, arr2)
        }
        3 => {
            let n1 = 1000usize;
            let n2 = 1000usize;
            let mut arr1 = Vec::with_capacity(n1);
            let mut i = 0usize;
            while i < n1 {
                arr1.push(i as i32);
                i += 1;
            }
            let mut arr2 = Vec::with_capacity(n2);
            let mut j = 0usize;
            while j < n2 {
                arr2.push((999 - j) as i32);
                j += 1;
            }
            (arr1, arr2)
        }
        4 => {
            let n1 = 1000usize;
            let mut arr1 = Vec::with_capacity(n1);
            let mut i = 0usize;
            while i < 500 {
                arr1.push(0);
                i += 1;
            }
            while i < 1000 {
                arr1.push(1000);
                i += 1;
            }
            let arr2 = vec![1000, 0];
            (arr1, arr2)
        }
        5 => {
            let mut arr1 = Vec::new();
            let mut i = 0usize;
            while i < 300 {
                arr1.push(5);
                i += 1;
            }
            while i < 600 {
                arr1.push(1);
                i += 1;
            }
            while i < 900 {
                arr1.push(9);
                i += 1;
            }
            while i < 1000 {
                arr1.push((i % 11) as i32);
                i += 1;
            }
            let arr2 = vec![9, 5, 1];
            (arr1, arr2)
        }
        6 => {
            let mut arr1 = Vec::new();
            let mut i = 0usize;
            while i < 1000 {
                arr1.push((1000 - (i % 1001)) as i32);
                i += 1;
            }
            let vals = sorted_unique_from_arr1(&arr1);
            let take = if vals.len() > 50 { 50 } else { vals.len() };
            let arr2 = build_arr2_from_subset(&vals[..take], 1, rng);
            (arr1, arr2)
        }
        7 => {
            let mut arr1 = Vec::new();
            let mut i = 0usize;
            while i < 1000 {
                let x = if i % 2 == 0 { 0 } else { 1000 };
                arr1.push(x);
                i += 1;
            }
            let arr2 = vec![0];
            (arr1, arr2)
        }
        8 => {
            let mut arr1 = Vec::new();
            let mut i = 0usize;
            while i < 1000 {
                arr1.push(((i * 37) % 1001) as i32);
                i += 1;
            }
            let vals = sorted_unique_from_arr1(&arr1);
            let start = if vals.len() > 20 { vals.len() - 20 } else { 0 };
            let arr2 = build_arr2_from_subset(&vals[start..], 2, rng);
            (arr1, arr2)
        }
        9 => {
            let mut arr1 = Vec::new();
            let mut x = 0i32;
            while x <= 1000 {
                let reps = if x % 3 == 0 { 2 } else { 1 };
                let mut k = 0;
                while k < reps && arr1.len() < 1000 {
                    arr1.push(x);
                    k += 1;
                }
                x += 1;
            }
            while arr1.len() < 1000 {
                arr1.push(1000);
            }
            let vals = sorted_unique_from_arr1(&arr1);
            let mut subset = Vec::new();
            let mut i = 0usize;
            while i < vals.len() {
                if i % 10 == 0 {
                    subset.push(vals[i]);
                }
                i += 1;
            }
            let arr2 = build_arr2_from_subset(&subset, 4, rng);
            (arr1, arr2)
        }
        _ => {
            let n1 = rng.gen_range_usize(1, 1000);
            let distinct_target = rng.gen_range_usize(1, if n1 < 40 { n1 } else { 40 });
            let mut values = Vec::new();
            while values.len() < distinct_target {
                let v = rng.gen_range_i32(0, 1000);
                if !contains(&values, v) {
                    values.push(v);
                }
            }

            let mut arr1 = Vec::with_capacity(n1);
            let mut i = 0usize;
            while i < values.len() && arr1.len() < n1 {
                arr1.push(values[i]);
                i += 1;
            }
            while arr1.len() < n1 {
                let idx = rng.gen_range_usize(0, values.len() - 1);
                arr1.push(values[idx]);
            }

            match rng.gen_range_usize(0, 3) {
                0 => {}
                1 => arr1.reverse(),
                2 => rng.shuffle(&mut arr1),
                _ => {
                    arr1.sort();
                    arr1.reverse();
                }
            }

            let max_k = if values.len() < 1000 { values.len() } else { 1000 };
            let k = rng.gen_range_usize(1, max_k);
            let mut subset = values.clone();
            rng.shuffle(&mut subset);
            subset.truncate(k);

            let arr2_mode = rng.gen_range_usize(0, 4);
            let arr2 = build_arr2_from_subset(&subset, arr2_mode, rng);
            (arr1, arr2)
        }
    }
}

fn print_json(arr1: &[i32], arr2: &[i32]) {
    print!("{{\"arr1\":[");
    let mut i = 0usize;
    while i < arr1.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", arr1[i]);
        i += 1;
    }
    print!("],\"arr2\":[");
    let mut j = 0usize;
    while j < arr2.len() {
        if j > 0 {
            print!(",");
        }
        print!("{}", arr2[j]);
        j += 1;
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

    let mut t = 0usize;
    while t < total {
        let mode = t % modes;
        let (arr1, arr2) = gen_case_mode(&mut rng, mode);
        let out = generate_test_case(arr1, arr2);
        print_json(&out.0, &out.1);
        t += 1;
    }
}