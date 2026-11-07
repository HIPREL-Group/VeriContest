use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
	pub open spec fn row_move_cost(row_costs: Seq<i32>, cur: int, target: int) -> int
		recommends
			0 <= cur < row_costs.len(),
			0 <= target < row_costs.len(),
			forall |i: int| 0 <= i < row_costs.len() ==> 0 <= #[trigger] row_costs[i] <= 10_000,
		decreases if cur <= target { target - cur } else { cur - target },
	{
		if cur == target {
			0
		} else if cur < target {
			row_costs[cur + 1] as int + Self::row_move_cost(row_costs, cur + 1, target)
		} else {
			row_costs[cur - 1] as int + Self::row_move_cost(row_costs, cur - 1, target)
		}
	}

	pub open spec fn col_move_cost(col_costs: Seq<i32>, cur: int, target: int) -> int
		recommends
			0 <= cur < col_costs.len(),
			0 <= target < col_costs.len(),
			forall |i: int| 0 <= i < col_costs.len() ==> 0 <= #[trigger] col_costs[i] <= 10_000,
		decreases if cur <= target { target - cur } else { cur - target },
	{
		if cur == target {
			0
		} else if cur < target {
			col_costs[cur + 1] as int + Self::col_move_cost(col_costs, cur + 1, target)
		} else {
			col_costs[cur - 1] as int + Self::col_move_cost(col_costs, cur - 1, target)
		}
	}

	pub fn min_cost(start_pos: Vec<i32>, home_pos: Vec<i32>, row_costs: Vec<i32>, col_costs: Vec<i32>) -> (result: i32)
		requires
			start_pos.len() == 2,
			home_pos.len() == 2,
			1 <= row_costs.len() <= 100_000,
			1 <= col_costs.len() <= 100_000,
			forall |i: int| 0 <= i < row_costs.len() ==> 0 <= #[trigger] row_costs[i] <= 10_000,
			forall |i: int| 0 <= i < col_costs.len() ==> 0 <= #[trigger] col_costs[i] <= 10_000,
			0 <= start_pos[0] < row_costs.len(),
			0 <= home_pos[0] < row_costs.len(),
			0 <= start_pos[1] < col_costs.len(),
			0 <= home_pos[1] < col_costs.len(),
		ensures
			result as int
				== Self::row_move_cost(row_costs@, start_pos[0] as int, home_pos[0] as int)
					+ Self::col_move_cost(col_costs@, start_pos[1] as int, home_pos[1] as int),
	{
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

}
