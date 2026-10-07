use vstd::prelude::*;

verus! {

pub open spec fn valid_negabinary(s: Seq<i32>) -> bool {
    1 <= s.len()
        && s.len() <= 1000
        && (forall|i: int| 0 <= i < s.len() ==> (#[trigger] s[i] == 0 || s[i] == 1))
        && (s.len() == 1 || s[0] == 1)
}

pub fn generate_test_case(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (out: (Vec<i32>, Vec<i32>))
    requires
        valid_negabinary(arr1@),
        valid_negabinary(arr2@),
    ensures
        valid_negabinary(out.0@),
        valid_negabinary(out.1@),
        out.0@ == arr1@,
        out.1@ == arr2@,
{
    let mut a: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < arr1.len()
        invariant
            i <= arr1.len(),
            a.len() == i,
            arr1.len() == arr1@.len(),
            valid_negabinary(arr1@),
            forall|k: int| 0 <= k < i as int ==> #[trigger] a[k] == arr1[k],
            forall|k: int| 0 <= k < i as int ==> (#[trigger] a[k] == 0 || a[k] == 1),
        decreases arr1.len() - i,
    {
        a.push(arr1[i]);
        i = i + 1;
    }

    let mut b: Vec<i32> = Vec::new();
    let mut j: usize = 0;
    while j < arr2.len()
        invariant
            j <= arr2.len(),
            b.len() == j,
            arr2.len() == arr2@.len(),
            valid_negabinary(arr2@),
            forall|k: int| 0 <= k < j as int ==> #[trigger] b[k] == arr2[k],
            forall|k: int| 0 <= k < j as int ==> (#[trigger] b[k] == 0 || b[k] == 1),
        decreases arr2.len() - j,
    {
        b.push(arr2[j]);
        j = j + 1;
    }

    proof {
        assert(a@ == arr1@) by {
            assert forall|k: int| 0 <= k < a.len() implies #[trigger] a[k] == arr1[k] by {};
        }
        assert(b@ == arr2@) by {
            assert forall|k: int| 0 <= k < b.len() implies #[trigger] b[k] == arr2[k] by {};
        }
        assert(valid_negabinary(a@));
        assert(valid_negabinary(b@));
    }

    (a, b)
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

    fn gen_bit(&mut self) -> i32 {
        (self.next_u64() & 1) as i32
    }
}

fn trim_leading_zeros(mut v: Vec<i32>) -> Vec<i32> {
    let mut i = 0usize;
    while i + 1 < v.len() && v[i] == 0 {
        i += 1;
    }
    if i == 0 {
        v
    } else {
        v.split_off(i)
    }
}

fn make_valid(bits: Vec<i32>) -> Vec<i32> {
    let mut v = if bits.is_empty() { vec![0] } else { bits };
    for x in &mut v {
        *x = if *x == 0 { 0 } else { 1 };
    }
    trim_leading_zeros(v)
}

fn rand_valid_array(rng: &mut Rng, len: usize) -> Vec<i32> {
    assert!(1 <= len && len <= 1000);
    if len == 1 {
        return vec![rng.gen_bit()];
    }
    let mut v = Vec::with_capacity(len);
    v.push(1);
    for _ in 1..len {
        v.push(rng.gen_bit());
    }
    v
}

fn alternating(len: usize, first: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for i in 0..len {
        v.push(if i % 2 == 0 { first } else { 1 - first });
    }
    make_valid(v)
}

fn one_hot(len: usize, pos: usize) -> Vec<i32> {
    let mut v = vec![0; len];
    v[pos] = 1;
    make_valid(v)
}

fn all_ones(len: usize) -> Vec<i32> {
    vec![1; len]
}

fn zeros_then_one(len: usize) -> Vec<i32> {
    let mut v = vec![0; len];
    v[len - 1] = 1;
    make_valid(v)
}

fn mode_case(rng: &mut Rng, mode: usize, t: usize) -> (Vec<i32>, Vec<i32>) {
    match mode {
        0 => (vec![0], vec![0]),
        1 => (vec![0], vec![1]),
        2 => (vec![1], vec![1]),
        3 => (all_ones(1000), all_ones(1000)),
        4 => (alternating(1000, 1), alternating(999, 1)),
        5 => (alternating(1000, 1), alternating(1000, 0)),
        6 => (one_hot(1000, 0), one_hot(1000, 999)),
        7 => (zeros_then_one(1000), vec![1]),
        8 => {
            let l1 = 1 + (t * 37 % 1000);
            let l2 = 1 + (t * 91 % 1000);
            (rand_valid_array(rng, l1), rand_valid_array(rng, l2))
        }
        9 => {
            let l = 2 + (t * 53 % 999);
            let mut a = rand_valid_array(rng, l);
            let b = a.clone();
            if a.len() > 1 {
                a[1] = 1 - a[1];
                a[0] = 1;
            }
            (make_valid(a), make_valid(b))
        }
        _ => {
            let l1 = if t % 2 == 0 { 1000 } else { 1 };
            let l2 = if t % 3 == 0 { 1000 } else { 2 + (t % 17) };
            (rand_valid_array(rng, l1), rand_valid_array(rng, l2))
        }
    }
}

fn print_json_array(v: &[i32]) {
    print!("[");
    for i in 0..v.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", v[i]);
    }
    print!("]");
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
        let (arr1, arr2) = mode_case(&mut rng, mode, t);
        let (a, b) = generate_test_case(&arr1, &arr2);
        print!("{{\"arr1\":");
        print_json_array(&a);
        print!(",\"arr2\":");
        print_json_array(&b);
        println!("}}");
    }
}