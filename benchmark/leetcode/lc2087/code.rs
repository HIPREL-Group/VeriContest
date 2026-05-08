impl Solution {
	pub fn min_cost(start_pos: Vec<i32>, home_pos: Vec<i32>, row_costs: Vec<i32>, col_costs: Vec<i32>) -> i32 {
		let mut r = start_pos[0];
		let mut c = start_pos[1];
		let sr = start_pos[0];
		let sc = start_pos[1];
		let hr = home_pos[0];
		let hc = home_pos[1];
		let mut result_i64: i64 = 0;

		if r < hr {
			while r < hr {
				r = r + 1;
				result_i64 = result_i64 + row_costs[r as usize] as i64;
			}
		} else {
			while r > hr {
				r = r - 1;
				result_i64 = result_i64 + row_costs[r as usize] as i64;
			}
		}

		if c < hc {
			while c < hc {
				c = c + 1;
				result_i64 = result_i64 + col_costs[c as usize] as i64;
			}
		} else {
			while c > hc {
				c = c - 1;
				result_i64 = result_i64 + col_costs[c as usize] as i64;
			}
		}

		result_i64 as i32
	}
}
