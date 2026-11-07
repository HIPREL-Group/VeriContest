use vstd::prelude::*;

verus! {

pub open spec fn valid_task(task: Seq<i32>) -> bool {
    task.len() == 2 && 1 <= task[0] <= 100 && 1 <= task[1] <= 100
}

pub fn generate_test_case(starts: Vec<i32>, durations: Vec<i32>) -> (result: Vec<Vec<i32>>)
    requires
        1 <= starts.len() <= 100,
        starts.len() == durations.len(),
        forall|i: int| 0 <= i < starts.len() ==> 1 <= #[trigger] starts[i] <= 100,
        forall|i: int| 0 <= i < durations.len() ==> 1 <= #[trigger] durations[i] <= 100,
    ensures
        1 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> #[trigger] valid_task(result[i]@),
{
    let n = starts.len();
    let mut tasks: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == starts.len(),
            n == durations.len(),
            1 <= n <= 100,
            0 <= i <= n,
            tasks.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] valid_task(tasks[j]@),
            forall|k: int| 0 <= k < starts.len() ==> 1 <= #[trigger] starts[k] <= 100,
            forall|k: int| 0 <= k < durations.len() ==> 1 <= #[trigger] durations[k] <= 100,
        decreases n - i,
    {
        let mut task: Vec<i32> = Vec::new();
        task.push(starts[i]);
        task.push(durations[i]);
        assert(task@.len() == 2);
        assert(task[0] == starts[i as int]);
        assert(task[1] == durations[i as int]);
        assert(valid_task(task@));
        tasks.push(task);
        i += 1;
    }
    tasks
}

} // verus!

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let range = (hi as i64 - lo as i64 + 1) as u64;
        (lo as i64 + (self.next_u64() % range) as i64) as i32
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3683);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |tasks_input: Vec<Vec<i32>>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", tasks_input);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::earliest_time(tasks_input.clone());
        writeln!(out, "{}", json!({"input": {"tasks": tasks_input}, "output": output})).unwrap();
        *count += 1;
    };

    // Example 1: tasks = [[1,6],[2,3]], output = 5
    {
        let starts = vec![1, 2];
        let durations = vec![6, 3];
        let tasks = generate_test_case(starts, durations);
        emit(tasks, &mut seen, &mut out, &mut count);
    }

    // Example 2: tasks = [[100,100],[100,100],[100,100]], output = 200
    {
        let starts = vec![100, 100, 100];
        let durations = vec![100, 100, 100];
        let tasks = generate_test_case(starts, durations);
        emit(tasks, &mut seen, &mut out, &mut count);
    }

    // Edge: single task
    {
        let starts = vec![1];
        let durations = vec![1];
        let tasks = generate_test_case(starts, durations);
        emit(tasks, &mut seen, &mut out, &mut count);
    }

    // Edge: single task max values
    {
        let starts = vec![100];
        let durations = vec![100];
        let tasks = generate_test_case(starts, durations);
        emit(tasks, &mut seen, &mut out, &mut count);
    }

    // Edge: two tasks, one clearly smallest
    {
        let starts = vec![1, 100];
        let durations = vec![1, 100];
        let tasks = generate_test_case(starts, durations);
        emit(tasks, &mut seen, &mut out, &mut count);
    }

    // Edge: all minimum values
    {
        let n = 100;
        let starts = vec![1; n];
        let durations = vec![1; n];
        let tasks = generate_test_case(starts, durations);
        emit(tasks, &mut seen, &mut out, &mut count);
    }

    // Edge: all maximum values
    {
        let n = 100;
        let starts = vec![100; n];
        let durations = vec![100; n];
        let tasks = generate_test_case(starts, durations);
        emit(tasks, &mut seen, &mut out, &mut count);
    }

    // Random test cases with diverse sizes
    while count < target {
        let n = match rng.next_u64() % 5 {
            0 => rng.gen_range_usize(1, 3),      // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 30),     // medium
            3 => rng.gen_range_usize(31, 70),     // large
            _ => rng.gen_range_usize(71, 100),    // max
        };

        let mut starts = Vec::with_capacity(n);
        let mut durations = Vec::with_capacity(n);
        for j in 0..n {
            // Mix boundary values ~20% of the time
            let s = if j % 5 == 0 {
                *[1i32, 100, 50, 1, 100].get(rng.gen_range_usize(0, 4)).unwrap()
            } else {
                rng.gen_range_i32(1, 100)
            };
            let d = if j % 5 == 0 {
                *[1i32, 100, 50, 1, 100].get(rng.gen_range_usize(0, 4)).unwrap()
            } else {
                rng.gen_range_i32(1, 100)
            };
            starts.push(s);
            durations.push(d);
        }

        let tasks = generate_test_case(starts, durations);
        emit(tasks, &mut seen, &mut out, &mut count);
    }
}
