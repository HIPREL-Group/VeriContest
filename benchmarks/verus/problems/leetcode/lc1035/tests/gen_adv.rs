use vstd::prelude::*;

verus! {

pub struct Solution;

pub open spec fn vec_all_in_range(v: Seq<i32>) -> bool {
    forall |i: int| 0 <= i < v.len() ==> 1 <= #[trigger] v[i] <= 2000
}

pub fn generate_test_case(
    nums1_fill: &Vec<i32>,
    nums2_fill: &Vec<i32>,
    special1: i32,
    special2: i32,
    idx1: usize,
    idx2: usize,
) -> (res: (Vec<i32>, Vec<i32>))
    requires
        0 <= idx1 <= nums1_fill.len(),
        0 <= idx2 <= nums2_fill.len(),
        1 <= nums1_fill.len() + 1 <= 500,
        1 <= nums2_fill.len() + 1 <= 500,
        1 <= special1 <= 2000,
        1 <= special2 <= 2000,
        forall |i: int| 0 <= i < nums1_fill.len() ==> 1 <= #[trigger] nums1_fill[i] <= 2000,
        forall |i: int| 0 <= i < nums2_fill.len() ==> 1 <= #[trigger] nums2_fill[i] <= 2000,
    ensures
        1 <= res.0.len() <= 500,
        1 <= res.1.len() <= 500,
        forall |i: int| 0 <= i < res.0.len() ==> 1 <= #[trigger] res.0[i] <= 2000,
        forall |i: int| 0 <= i < res.1.len() ==> 1 <= #[trigger] res.1[i] <= 2000,
{
    let mut a: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < nums1_fill.len()
        invariant
            0 <= i <= nums1_fill.len(),
            a.len() == i,
            forall |k: int| 0 <= k < i ==> #[trigger] a[k] == nums1_fill[k],
            forall |k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= 2000,
            forall |k: int| 0 <= k < nums1_fill.len() ==> 1 <= #[trigger] nums1_fill[k] <= 2000,
        decreases nums1_fill.len() - i,
    {
        a.push(nums1_fill[i]);
        i = i + 1;
    }
    a.insert(idx1, special1);

    let mut b: Vec<i32> = Vec::new();
    let mut j: usize = 0;
    while j < nums2_fill.len()
        invariant
            0 <= j <= nums2_fill.len(),
            b.len() == j,
            forall |k: int| 0 <= k < j ==> #[trigger] b[k] == nums2_fill[k],
            forall |k: int| 0 <= k < b.len() ==> 1 <= #[trigger] b[k] <= 2000,
            forall |k: int| 0 <= k < nums2_fill.len() ==> 1 <= #[trigger] nums2_fill[k] <= 2000,
        decreases nums2_fill.len() - j,
    {
        b.push(nums2_fill[j]);
        j = j + 1;
    }
    b.insert(idx2, special2);

    assert(a.len() == nums1_fill.len() + 1);
    assert(b.len() == nums2_fill.len() + 1);
    assert(1 <= a.len() <= 500);
    assert(1 <= b.len() <= 500);

    assert forall |k: int| 0 <= k < a.len() implies 1 <= #[trigger] a[k] <= 2000 by {
        if k < idx1 as int {
            assert(a[k] == nums1_fill[k]);
        } else if k == idx1 as int {
            assert(a[k] == special1);
        } else {
            assert(a[k] == nums1_fill[k - 1]);
        }
    };

    assert forall |k: int| 0 <= k < b.len() implies 1 <= #[trigger] b[k] <= 2000 by {
        if k < idx2 as int {
            assert(b[k] == nums2_fill[k]);
        } else if k == idx2 as int {
            assert(b[k] == special2);
        } else {
            assert(b[k] == nums2_fill[k - 1]);
        }
    };

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
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize % (hi - lo + 1))
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        lo + (self.next_u64() % ((hi - lo + 1) as u64)) as i32
    }

    fn shuffle(&mut self, v: &mut [i32]) {
        let n = v.len();
        if n <= 1 {
            return;
        }
        let mut i = n - 1;
        while i > 0 {
            let j = self.gen_range_usize(0, i);
            v.swap(i, j);
            i -= 1;
        }
    }
}

fn make_fill(rng: &mut Rng, len: usize, bias: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    let mut i = 0usize;
    while i < len {
        let x = match i % 5 {
            0 => bias,
            1 => ((bias + 1 - 1) % 2000) + 1,
            2 => 1,
            3 => 2000,
            _ => rng.gen_range_i32(1, 2000),
        };
        v.push(x);
        i += 1;
    }
    v
}

fn mode_case(rng: &mut Rng, mode: usize) -> (Vec<i32>, Vec<i32>, i32, i32, usize, usize) {
    match mode {
        0 => {
            let n1 = 499;
            let n2 = 499;
            (make_fill(rng, n1, 1), make_fill(rng, n2, 1), 1, 1, 0, 0)
        }
        1 => {
            let n1 = 499;
            let n2 = 499;
            (make_fill(rng, n1, 2000), make_fill(rng, n2, 2000), 2000, 2000, n1, n2)
        }
        2 => {
            let n1 = 0;
            let n2 = 0;
            (vec![], vec![], 1, 2000, 0, 0)
        }
        3 => {
            let n1 = 499;
            let n2 = 0;
            (make_fill(rng, n1, 7), vec![], 7, 7, n1 / 2, 0)
        }
        4 => {
            let n1 = 0;
            let n2 = 499;
            (vec![], make_fill(rng, n2, 9), 9, 9, 0, n2 / 2)
        }
        5 => {
            let n1 = 499;
            let n2 = 499;
            let mut a = vec![1; n1];
            let mut b = vec![1; n2];
            if n1 > 0 { a[n1 / 3] = 2000; }
            if n2 > 0 { b[n2 / 4] = 2000; }
            (a, b, 2000, 2000, 0, n2)
        }
        6 => {
            let n1 = 499;
            let n2 = 499;
            let mut a = Vec::with_capacity(n1);
            let mut b = Vec::with_capacity(n2);
            let mut i = 0usize;
            while i < n1 {
                a.push((i % 20 + 1) as i32);
                i += 1;
            }
            let mut j = 0usize;
            while j < n2 {
                b.push((((n2 - 1 - j) % 20) + 1) as i32);
                j += 1;
            }
            (a, b, 13, 13, n1 / 2, n2 / 2)
        }
        7 => {
            let n1 = 499;
            let n2 = 499;
            let mut a = make_fill(rng, n1, 1000);
            let mut b = make_fill(rng, n2, 1000);
            rng.shuffle(&mut a);
            rng.shuffle(&mut b);
            (a, b, 1000, 1000, 1, n2 - 1)
        }
        8 => {
            let n1 = 499;
            let n2 = 499;
            let mut a = Vec::with_capacity(n1);
            let mut b = Vec::with_capacity(n2);
            let mut i = 0usize;
            while i < n1 {
                a.push(((i % 2) + 1) as i32);
                i += 1;
            }
            let mut j = 0usize;
            while j < n2 {
                b.push((((j + 1) % 2) + 1) as i32);
                j += 1;
            }
            (a, b, 2, 2, n1, 0)
        }
        9 => {
            let n1 = rng.gen_range_usize(0, 499);
            let n2 = rng.gen_range_usize(0, 499);
            let s = rng.gen_range_i32(1, 2000);
            let t = rng.gen_range_i32(1, 2000);
            (
                make_fill(rng, n1, s),
                make_fill(rng, n2, t),
                s,
                t,
                rng.gen_range_usize(0, n1),
                rng.gen_range_usize(0, n2),
            )
        }
        _ => {
            let n1 = 499;
            let n2 = 499;
            (
                make_fill(rng, n1, 123),
                make_fill(rng, n2, 456),
                123,
                456,
                250,
                250,
            )
        }
    }
}

fn print_vec(v: &[i32], out: &mut String) {
    out.push('[');
    let mut i = 0usize;
    while i < v.len() {
        if i > 0 {
            out.push(',');
        }
        out.push_str(&v[i].to_string());
        i += 1;
    }
    out.push(']');
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
    let mut case_id = 0usize;

    while case_id < total {
        let mode = if case_id < 120 {
            case_id % 10
        } else {
            rng.gen_range_usize(0, 9)
        };

        let (fill1, fill2, special1, special2, idx1, idx2) = mode_case(&mut rng, mode);
        let (nums1, nums2) = generate_test_case(&fill1, &fill2, special1, special2, idx1, idx2);

        let mut line = String::new();
        line.push_str("{\"nums1\":");
        print_vec(&nums1, &mut line);
        line.push_str(",\"nums2\":");
        print_vec(&nums2, &mut line);
        line.push('}');
        println!("{}", line);

        case_id += 1;
    }
}