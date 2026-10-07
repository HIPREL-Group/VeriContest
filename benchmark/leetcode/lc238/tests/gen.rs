use vstd::prelude::*;

verus! {

pub open spec fn product_of_range(nums: Seq<i32>, start: int, end: int) -> int
    decreases end - start
{
    if start >= end {
        1
    } else {
        nums[start] as int * product_of_range(nums, start + 1, end)
    }
}

proof fn lemma_product_unit(nums: Seq<i32>, start: int, end: int)
    requires
        0 <= start,
        end <= nums.len() as int,
        forall|i: int| start <= i < end ==> -1 <= #[trigger] nums[i] <= 1,
    ensures
        -1 <= product_of_range(nums, start, end) <= 1,
    decreases end - start
{
    if start >= end {
    } else {
        lemma_product_unit(nums, start + 1, end);
        let val = nums[start] as int;
        let rest = product_of_range(nums, start + 1, end);
        assert(-1 <= val <= 1);
        assert(-1 <= rest <= 1);
        assert(-1 <= val * rest <= 1) by(nonlinear_arith)
            requires -1 <= val <= 1, -1 <= rest <= 1;
    }
}

proof fn prove_products_bounded(nums: Seq<i32>)
    requires
        2 <= nums.len() <= 100_000,
        forall|i: int| 0 <= i < nums.len() ==> -1 <= #[trigger] nums[i] <= 1,
    ensures
        forall|i: int| 0 <= i < nums.len() ==> -30 <= #[trigger] nums[i] <= 30,
        forall|i: int| 0 <= i < nums.len() ==>
            i32::MIN <= #[trigger] product_of_range(nums, 0, i) *
            product_of_range(nums, i + 1, nums.len() as int) <= i32::MAX,
        forall|i: int| 0 <= i <= nums.len() ==>
            i32::MIN <= #[trigger] product_of_range(nums, 0, i) <= i32::MAX,
        forall|i: int| 0 <= i <= nums.len() ==>
            i32::MIN <= #[trigger] product_of_range(nums, i, nums.len() as int) <= i32::MAX,
{
    assert forall|i: int| 0 <= i <= nums.len() implies
        -1 <= #[trigger] product_of_range(nums, 0, i) <= 1
    by { lemma_product_unit(nums, 0, i); };

    assert forall|i: int| 0 <= i <= nums.len() implies
        -1 <= #[trigger] product_of_range(nums, i, nums.len() as int) <= 1
    by { lemma_product_unit(nums, i, nums.len() as int); };

    assert forall|i: int| 0 <= i < nums.len() implies
        i32::MIN <= #[trigger] product_of_range(nums, 0, i) *
        product_of_range(nums, i + 1, nums.len() as int) <= i32::MAX
    by {
        lemma_product_unit(nums, 0, i);
        lemma_product_unit(nums, i + 1, nums.len() as int);
        let a = product_of_range(nums, 0, i);
        let b = product_of_range(nums, i + 1, nums.len() as int);
        assert(-1 <= a <= 1);
        assert(-1 <= b <= 1);
        assert(-1 <= a * b <= 1) by(nonlinear_arith)
            requires -1 <= a <= 1, -1 <= b <= 1;
    };
}

pub fn generate_test_case(elems: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        2 <= elems.len() <= 100_000,
        forall|i: int| 0 <= i < elems.len() ==> -1 <= #[trigger] elems[i] <= 1,
    ensures
        2 <= result.len() <= 100_000,
        forall|i: int| 0 <= i < result.len() ==> -30 <= #[trigger] result[i] <= 30,
        forall|i: int| 0 <= i < result.len() ==>
            i32::MIN <= #[trigger] product_of_range(result@, 0, i) *
            product_of_range(result@, i + 1, result@.len() as int) <= i32::MAX,
        forall|i: int| 0 <= i <= result.len() ==>
            i32::MIN <= #[trigger] product_of_range(result@, 0, i) <= i32::MAX,
        forall|i: int| 0 <= i <= result.len() ==>
            i32::MIN <= #[trigger] product_of_range(result@, i, result@.len() as int) <= i32::MAX,
{
    if mutation_kind == 0 {
        // identity
        proof { prove_products_bounded(elems@); }
        elems
    } else if mutation_kind == 1 {
        // set first element to 0
        let mut d = elems;
        d.set(0, 0);
        proof {
            assert forall|i: int| 0 <= i < d.len() implies -1 <= #[trigger] d[i] <= 1 by {
                if i == 0 { } else { }
            };
            prove_products_bounded(d@);
        }
        d
    } else if mutation_kind == 2 {
        // set last element to 0
        let mut d = elems;
        let last = d.len() - 1;
        d.set(last, 0);
        proof {
            assert forall|i: int| 0 <= i < d.len() implies -1 <= #[trigger] d[i] <= 1 by {
                if i == last as int { } else { }
            };
            prove_products_bounded(d@);
        }
        d
    } else if mutation_kind == 3 {
        // set first element to 1
        let mut d = elems;
        d.set(0, 1);
        proof {
            assert forall|i: int| 0 <= i < d.len() implies -1 <= #[trigger] d[i] <= 1 by {
                if i == 0 { } else { }
            };
            prove_products_bounded(d@);
        }
        d
    } else if mutation_kind == 4 {
        // set first element to -1
        let mut d = elems;
        d.set(0, -1);
        proof {
            assert forall|i: int| 0 <= i < d.len() implies -1 <= #[trigger] d[i] <= 1 by {
                if i == 0 { } else { }
            };
            prove_products_bounded(d@);
        }
        d
    } else if mutation_kind == 5 {
        // negate first element
        let mut d = elems;
        let v = -d[0];
        d.set(0, v);
        proof {
            assert forall|i: int| 0 <= i < d.len() implies -1 <= #[trigger] d[i] <= 1 by {
                if i == 0 { } else { }
            };
            prove_products_bounded(d@);
        }
        d
    } else if mutation_kind == 6 && elems.len() < 100_000 {
        // grow by one (push 1)
        let mut d = elems;
        d.push(1);
        proof {
            assert forall|i: int| 0 <= i < d.len() implies -1 <= #[trigger] d[i] <= 1 by {
                if i < elems.len() as int { } else { }
            };
            prove_products_bounded(d@);
        }
        d
    } else if mutation_kind == 7 && elems.len() > 2 {
        // shrink by one (pop)
        let mut d = elems;
        d.pop();
        proof {
            assert forall|i: int| 0 <= i < d.len() implies -1 <= #[trigger] d[i] <= 1 by {};
            prove_products_bounded(d@);
        }
        d
    } else if mutation_kind == 8 {
        // set all elements to 0
        let mut d = elems;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == elems.len(),
                2 <= d.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> d[j] == 0,
                forall|j: int| i <= j < d.len() ==> d[j] == elems[j],
            decreases d.len() - i,
        {
            d.set(i, 0);
            i += 1;
        }
        proof {
            assert forall|i: int| 0 <= i < d.len() implies -1 <= #[trigger] d[i] <= 1 by {};
            prove_products_bounded(d@);
        }
        d
    } else if mutation_kind == 9 {
        // swap first and last elements
        let mut d = elems;
        let last = d.len() - 1;
        let first_val = d[0];
        let last_val = d[last];
        d.set(0, last_val);
        d.set(last, first_val);
        proof {
            assert forall|i: int| 0 <= i < d.len() implies -1 <= #[trigger] d[i] <= 1 by {
                if i == 0 {
                } else if i == last as int {
                } else { }
            };
            prove_products_bounded(d@);
        }
        d
    } else {
        // fallback: identity
        proof { prove_products_bounded(elems@); }
        elems
    }
}

} // verus!

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn mutate(elems: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(elems, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_unit_array(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(-1, 1) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>, total: &mut usize| {
        if *total >= count {
            return;
        }
        let key = format!("{:?}", nums);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::product_except_self(nums.clone());
        writeln!(out, "{}", json!({
            "input": {"nums": nums},
            "output": output
        })).unwrap();
        *total += 1;
    };

    // Example inputs from description.md
    emit(vec![1, 2, 3, 4], &mut seen, &mut out, &mut total);
    emit(vec![-1, 1, 0, -3, 3], &mut seen, &mut out, &mut total);

    // Structured seed arrays
    let seeds: Vec<Vec<i32>> = vec![
        vec![1, 1],
        vec![-1, -1],
        vec![0, 0],
        vec![1, 0],
        vec![0, 1],
        vec![1, -1],
        vec![-1, 1],
        vec![-1, 0],
        vec![0, -1],
        vec![1, 1, 1],
        vec![-1, -1, -1],
        vec![0, 0, 0],
        vec![1, 0, -1],
        vec![1, 1, 0, -1, -1],
        vec![0, 1, 0, 1, 0],
        vec![1, -1, 1, -1, 1, -1],
        vec![1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut total);
        }
    }

    let size_classes: Vec<(usize, usize)> = vec![
        (2, 3),
        (4, 10),
        (11, 50),
        (51, 200),
        (201, 1000),
    ];

    for &(lo, hi) in &size_classes {
        for _ in 0..8 {
            if total >= count { break; }
            let len = rng.gen_range_usize(lo, hi);
            let arr = random_unit_array(&mut rng, len);
            let mk = rng.gen_range_usize(0, 9) as u8;
            let result = mutate(arr, mk);
            emit(result, &mut seen, &mut out, &mut total);
        }
    }

    while total < count {
        let len = match total % 5 {
            0 => rng.gen_range_usize(2, 5),
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 500),
            _ => rng.gen_range_usize(501, 2000),
        };
        let arr = random_unit_array(&mut rng, len);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = mutate(arr, mk);
        emit(result, &mut seen, &mut out, &mut total);
    }
}
