use vstd::prelude::*;

verus! {

pub open spec fn total_len(arrays: Seq<Vec<i32>>) -> int
    decreases arrays.len(),
{
    if arrays.len() == 0 {
        0
    } else {
        arrays[0].len() + total_len(arrays.drop_first())
    }
}

proof fn lemma_total_len_two(s: Seq<Vec<i32>>)
    requires
        s.len() == 2,
    ensures
        total_len(s) == s[0].len() + s[1].len(),
{
    reveal_with_fuel(total_len, 3);
    assert(s.drop_first() =~= seq![s[1]]);
    assert(seq![s[1]].drop_first() =~= Seq::<Vec<i32>>::empty());
}

proof fn lemma_total_len_three(s: Seq<Vec<i32>>)
    requires
        s.len() == 3,
    ensures
        total_len(s) == s[0].len() + s[1].len() + s[2].len(),
{
    reveal_with_fuel(total_len, 4);
    assert(s.drop_first() =~= seq![s[1], s[2]]);
    assert(seq![s[1], s[2]].drop_first() =~= seq![s[2]]);
    assert(seq![s[2]].drop_first() =~= Seq::<Vec<i32>>::empty());
}

pub fn generate_test_case(
    arr1: Vec<i32>,
    arr2: Vec<i32>,
    mutation_kind: u8,
) -> (result: Vec<Vec<i32>>)
    requires
        1 <= arr1.len() <= 500,
        1 <= arr2.len() <= 500,
        arr1.len() + arr2.len() <= 1000,
        forall|i: int| 0 <= i < arr1.len() ==> -10_000 <= #[trigger] arr1[i] <= 10_000,
        forall|i: int| 0 <= i < arr2.len() ==> -10_000 <= #[trigger] arr2[i] <= 10_000,
        forall|i: int, j: int| 0 <= i < j < arr1.len() ==> arr1[i] <= arr1[j],
        forall|i: int, j: int| 0 <= i < j < arr2.len() ==> arr2[i] <= arr2[j],
    ensures
        2 <= result.len() <= 100_000,
        forall|a: int| 0 <= a < result.len() ==> 1 <= #[trigger] result[a].len() <= 500,
        total_len(result@) <= 100_000,
        forall|a: int, i: int| 0 <= a < result.len() && 0 <= i < result[a].len() ==>
            -10_000 <= #[trigger] result[a][i] <= 10_000,
        forall|a: int, i: int, j: int|
            0 <= a < result.len() && 0 <= i < j < result[a].len() ==>
            result[a][i] <= result[a][j],
{
    if mutation_kind == 1 {
        // Swap order of arrays
        let mut arrays: Vec<Vec<i32>> = Vec::new();
        arrays.push(arr2);
        arrays.push(arr1);
        proof {
            lemma_total_len_two(arrays@);
            assert forall|a: int| 0 <= a < arrays.len() implies
                1 <= #[trigger] arrays[a].len() <= 500 by {
                if a == 0 {
                    assert(arrays[a] == arr2);
                } else {
                    assert(arrays[a] == arr1);
                }
            };
            assert forall|a: int, i: int|
                0 <= a < arrays.len() && 0 <= i < arrays[a].len() implies
                -10_000 <= #[trigger] arrays[a][i] <= 10_000 by {
                if a == 0 {
                    assert(arrays[a] == arr2);
                } else {
                    assert(arrays[a] == arr1);
                }
            };
            assert forall|a: int, i: int, j: int|
                0 <= a < arrays.len() && 0 <= i < j < arrays[a].len() implies
                arrays[a][i] <= arrays[a][j] by {
                if a == 0 {
                    assert(arrays[a] == arr2);
                } else {
                    assert(arrays[a] == arr1);
                }
            };
        }
        arrays
    } else if mutation_kind == 2 {
        // Replace arr1 with single-element [-10_000] (boundary minimum)
        let mut a_min: Vec<i32> = Vec::new();
        a_min.push(-10_000i32);
        let mut arrays: Vec<Vec<i32>> = Vec::new();
        arrays.push(a_min);
        arrays.push(arr2);
        proof {
            lemma_total_len_two(arrays@);
            assert forall|a: int| 0 <= a < arrays.len() implies
                1 <= #[trigger] arrays[a].len() <= 500 by {
                if a == 0 {
                    assert(arrays[0].len() == 1);
                } else {
                    assert(arrays[a] == arr2);
                }
            };
            assert forall|a: int, i: int|
                0 <= a < arrays.len() && 0 <= i < arrays[a].len() implies
                -10_000 <= #[trigger] arrays[a][i] <= 10_000 by {
                if a == 0 {
                    assert(arrays[0][0] == -10_000);
                } else {
                    assert(arrays[a] == arr2);
                }
            };
            assert forall|a: int, i: int, j: int|
                0 <= a < arrays.len() && 0 <= i < j < arrays[a].len() implies
                arrays[a][i] <= arrays[a][j] by {
                if a == 0 {
                    assert(arrays[0].len() == 1);
                    assert(false);
                } else {
                    assert(arrays[a] == arr2);
                }
            };
        }
        arrays
    } else if mutation_kind == 3 {
        // Replace arr2 with single-element [10_000] (boundary maximum)
        let mut a_max: Vec<i32> = Vec::new();
        a_max.push(10_000i32);
        let mut arrays: Vec<Vec<i32>> = Vec::new();
        arrays.push(arr1);
        arrays.push(a_max);
        proof {
            lemma_total_len_two(arrays@);
            assert forall|a: int| 0 <= a < arrays.len() implies
                1 <= #[trigger] arrays[a].len() <= 500 by {
                if a == 0 {
                    assert(arrays[a] == arr1);
                } else {
                    assert(arrays[1].len() == 1);
                }
            };
            assert forall|a: int, i: int|
                0 <= a < arrays.len() && 0 <= i < arrays[a].len() implies
                -10_000 <= #[trigger] arrays[a][i] <= 10_000 by {
                if a == 0 {
                    assert(arrays[a] == arr1);
                } else {
                    assert(arrays[1][0] == 10_000);
                }
            };
            assert forall|a: int, i: int, j: int|
                0 <= a < arrays.len() && 0 <= i < j < arrays[a].len() implies
                arrays[a][i] <= arrays[a][j] by {
                if a == 0 {
                    assert(arrays[a] == arr1);
                } else {
                    assert(arrays[1].len() == 1);
                    assert(false);
                }
            };
        }
        arrays
    } else if mutation_kind == 4 {
        // Two single-element boundary arrays: [[-10_000], [10_000]]
        let mut a_min: Vec<i32> = Vec::new();
        a_min.push(-10_000i32);
        let mut a_max: Vec<i32> = Vec::new();
        a_max.push(10_000i32);
        let mut arrays: Vec<Vec<i32>> = Vec::new();
        arrays.push(a_min);
        arrays.push(a_max);
        proof {
            lemma_total_len_two(arrays@);
            assert forall|a: int| 0 <= a < arrays.len() implies
                1 <= #[trigger] arrays[a].len() <= 500 by {
                if a == 0 {
                    assert(arrays[0].len() == 1);
                } else {
                    assert(arrays[1].len() == 1);
                }
            };
            assert forall|a: int, i: int|
                0 <= a < arrays.len() && 0 <= i < arrays[a].len() implies
                -10_000 <= #[trigger] arrays[a][i] <= 10_000 by {
                if a == 0 {
                    assert(arrays[0][0] == -10_000);
                } else {
                    assert(arrays[1][0] == 10_000);
                }
            };
            assert forall|a: int, i: int, j: int|
                0 <= a < arrays.len() && 0 <= i < j < arrays[a].len() implies
                arrays[a][i] <= arrays[a][j] by {
                if a == 0 {
                    assert(arrays[0].len() == 1);
                    assert(false);
                } else {
                    assert(arrays[1].len() == 1);
                    assert(false);
                }
            };
        }
        arrays
    } else if mutation_kind == 5 && arr1.len() + arr2.len() < 1000 {
        // Three arrays: [arr1, arr2, [0]]
        let mut a3: Vec<i32> = Vec::new();
        a3.push(0i32);
        let mut arrays: Vec<Vec<i32>> = Vec::new();
        arrays.push(arr1);
        arrays.push(arr2);
        arrays.push(a3);
        proof {
            lemma_total_len_three(arrays@);
            assert forall|a: int| 0 <= a < arrays.len() implies
                1 <= #[trigger] arrays[a].len() <= 500 by {
                if a == 0 {
                    assert(arrays[a] == arr1);
                } else if a == 1 {
                    assert(arrays[a] == arr2);
                } else {
                    assert(arrays[2].len() == 1);
                }
            };
            assert forall|a: int, i: int|
                0 <= a < arrays.len() && 0 <= i < arrays[a].len() implies
                -10_000 <= #[trigger] arrays[a][i] <= 10_000 by {
                if a == 0 {
                    assert(arrays[a] == arr1);
                } else if a == 1 {
                    assert(arrays[a] == arr2);
                } else {
                    assert(arrays[2][0] == 0);
                }
            };
            assert forall|a: int, i: int, j: int|
                0 <= a < arrays.len() && 0 <= i < j < arrays[a].len() implies
                arrays[a][i] <= arrays[a][j] by {
                if a == 0 {
                    assert(arrays[a] == arr1);
                } else if a == 1 {
                    assert(arrays[a] == arr2);
                } else {
                    assert(arrays[2].len() == 1);
                    assert(false);
                }
            };
        }
        arrays
    } else {
        // Base: [arr1, arr2]
        let mut arrays: Vec<Vec<i32>> = Vec::new();
        arrays.push(arr1);
        arrays.push(arr2);
        proof {
            lemma_total_len_two(arrays@);
            assert forall|a: int| 0 <= a < arrays.len() implies
                1 <= #[trigger] arrays[a].len() <= 500 by {
                if a == 0 {
                    assert(arrays[a] == arr1);
                } else {
                    assert(arrays[a] == arr2);
                }
            };
            assert forall|a: int, i: int|
                0 <= a < arrays.len() && 0 <= i < arrays[a].len() implies
                -10_000 <= #[trigger] arrays[a][i] <= 10_000 by {
                if a == 0 {
                    assert(arrays[a] == arr1);
                } else {
                    assert(arrays[a] == arr2);
                }
            };
            assert forall|a: int, i: int, j: int|
                0 <= a < arrays.len() && 0 <= i < j < arrays[a].len() implies
                arrays[a][i] <= arrays[a][j] by {
                if a == 0 {
                    assert(arrays[a] == arr1);
                } else {
                    assert(arrays[a] == arr2);
                }
            };
        }
        arrays
    }
}

} // verus!

extern crate serde_json;
use serde_json::json;

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

fn random_sorted_array(rng: &mut Rng, len: usize, lo: i64, hi: i64) -> Vec<i32> {
    let mut arr: Vec<i32> = (0..len).map(|_| rng.gen_range_i64(lo, hi) as i32).collect();
    arr.sort();
    arr
}

fn main() {
    use std::io::Write;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut emitted = 0usize;

    // Example inputs from description.md (emitted directly, not through generator)
    let examples: Vec<Vec<Vec<i32>>> = vec![
        vec![vec![1, 2, 3], vec![4, 5], vec![1, 2, 3]],
        vec![vec![1], vec![1]],
    ];
    for arrays in examples {
        if emitted >= count { break; }
        let output = Solution::max_distance(arrays.clone());
        writeln!(out, "{}", json!({"input": {"arrays": arrays}, "output": output})).unwrap();
        emitted += 1;
    }

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5];

    // Boundary seed pairs
    let boundary_pairs: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![-10_000], vec![10_000]),
        (vec![0], vec![0]),
        (vec![-10_000, -5_000, 0, 5_000, 10_000], vec![-10_000, -5_000, 0, 5_000, 10_000]),
        (vec![-10_000], vec![-10_000]),
        (vec![10_000], vec![10_000]),
        (vec![0, 0, 0], vec![0, 0, 0]),
        (vec![-10_000, 10_000], vec![-10_000, 10_000]),
    ];
    for (a1, a2) in &boundary_pairs {
        for &mk in &mutation_kinds {
            if emitted >= count { break; }
            let arrays = generate_test_case(a1.clone(), a2.clone(), mk);
            let output = Solution::max_distance(arrays.clone());
            writeln!(out, "{}", json!({"input": {"arrays": arrays}, "output": output})).unwrap();
            emitted += 1;
        }
    }

    // Diverse random test cases
    while emitted < count {
        let n1: usize = match emitted % 5 {
            0 => 1,
            1 => rng.gen_range_usize(1, 5),
            2 => rng.gen_range_usize(5, 50),
            3 => rng.gen_range_usize(50, 200),
            _ => rng.gen_range_usize(200, 500),
        };
        let max_n2 = 1000 - n1;
        let n2: usize = match (emitted + 2) % 5 {
            0 => 1,
            1 => rng.gen_range_usize(1, std::cmp::min(5, max_n2)),
            2 => rng.gen_range_usize(1, std::cmp::min(50, max_n2)),
            3 => rng.gen_range_usize(1, std::cmp::min(200, max_n2)),
            _ => rng.gen_range_usize(1, std::cmp::min(500, max_n2)),
        };

        let (lo, hi): (i64, i64) = match emitted % 4 {
            0 => (-10_000, 10_000),
            1 => (-100, 100),
            2 => (0, 10_000),
            _ => (-10_000, 0),
        };

        let arr1 = random_sorted_array(&mut rng, n1, lo, hi);
        let arr2 = random_sorted_array(&mut rng, n2, lo, hi);
        let mk = mutation_kinds[rng.gen_range_usize(0, mutation_kinds.len() - 1)];
        let arrays = generate_test_case(arr1, arr2, mk);
        let output = Solution::max_distance(arrays.clone());
        writeln!(out, "{}", json!({"input": {"arrays": arrays}, "output": output})).unwrap();
        emitted += 1;
    }
}
