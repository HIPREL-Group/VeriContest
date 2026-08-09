impl Solution {
    pub fn create_sorted_array(instructions: Vec<i32>) -> i32 {
        let mut cost: i64 = 0;
        let n = instructions.len();
        let block_size: usize = 320;
        let num_blocks: usize = 313;

        let mut freq: Vec<i64> = Vec::new();
        let mut fi: usize = 0;
        while fi < 100_000 {
            freq.push(0);
            fi = fi + 1;
        }

        let mut block_sum: Vec<i64> = Vec::new();
        let mut bi: usize = 0;
        while bi < num_blocks {
            block_sum.push(0);
            bi = bi + 1;
        }

        let mut i: usize = 0;
        while i < n {
            let val = instructions[i] as usize;
            let b0 = val / block_size;

            let mut sum: i64 = 0;
            let mut bb: usize = 0;
            while bb < b0 {
                sum = sum + block_sum[bb];
                bb = bb + 1;
            }

            let mut p: usize = b0 * block_size;
            while p < val {
                sum = sum + freq[p];
                p = p + 1;
            }
            let leq = sum;

            let less = leq - freq[val - 1];
            let greater = (i as i64) - leq;

            let min_cost: i64 = if less < greater { less } else { greater };
            cost = cost + min_cost;

            let pos = val - 1;
            freq[pos] = freq[pos] + 1;
            let block_idx = pos / block_size;
            block_sum[block_idx] = block_sum[block_idx] + 1;

            i = i + 1;
        }
        (cost % 1_000_000_007) as i32
    }
}
